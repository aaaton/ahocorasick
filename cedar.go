package cedar

import (
	"bytes"
	"errors"
	"fmt"
	"io/ioutil"
)

// defines max & min value of chinese CJK code
const (
	valueLimit = int(^uint(0) >> 1)
	CJKZhMin   = '\u4E00'
	CJKZhMax   = '\u9FFF'
	acsiiMax   = '\u007F'
	asciiA     = 'A'
	asciiz     = 'z'
)

type Node struct {
	Value int
	Check int
}

type nvalue struct {
	len   int
	Value interface{}
}

type ndesc struct {
	Label byte
	ID    int
}

func (n *Node) base() int { return -(n.Value + 1) }

type ninfo struct {
	Sibling byte
	Child   byte
	End     bool
}

type block struct {
	Prev, Next, Num, reject, Trial, Ehead int
}

func (b *block) init() {
	b.Num = 256
	b.reject = 257
}

// Cedar encapsulates a fast and compressed double Array trie for words query
type Cedar struct {
	Array    []Node
	Infos    []ninfo
	Blocks   []block
	Vals     map[int]nvalue
	vkey     int
	reject   [257]int
	bheadF   int
	bheadC   int
	bheadO   int
	Capacity int
	Size     int
	ordered  bool
	maxTrial int
}

// NewCedar new a Cedar instance
func NewCedar() *Cedar {
	da := Cedar{
		Array:    make([]Node, 256),
		Infos:    make([]ninfo, 256),
		Blocks:   make([]block, 1),
		Capacity: 256,
		Size:     256,
		Vals:     make(map[int]nvalue),
		vkey:     1,
		ordered:  true,
		maxTrial: 1,
	}

	da.Array[0] = Node{-2, 0}
	for i := 1; i < 256; i++ {
		da.Array[i] = Node{-(i - 1), -(i + 1)}
	}
	da.Array[1].Value = -255
	da.Array[255].Check = -1

	da.Blocks[0].Ehead = 1
	da.Blocks[0].init()

	for i := 0; i <= 256; i++ {
		da.reject[i] = i + 1
	}

	return &da
}

func (da *Cedar) vKey() int {
	k := da.vkey
	for {
		k = (k + 1) % da.Capacity
		if _, ok := da.Vals[k]; !ok {
			break
		}
	}
	da.vkey = k
	return k
}

func (da *Cedar) keyLen(id int) int {
	val, err := da.vKeyOf(id)
	if err != nil {
		return 0
	}
	if v, ok := da.Vals[val]; ok {
		return v.len
	}
	return 0
}

// Get value by key, insert the key if not exist
func (da *Cedar) get(key []byte, from, pos int) int {
	for ; pos < len(key); pos++ {
		if value := da.Array[from].Value; value >= 0 && value != valueLimit {
			to := da.follow(from, 0)
			da.Array[to].Value = value
		}
		from = da.follow(from, key[pos])
	}
	to := from
	if da.Array[from].Value < 0 {
		to = da.follow(from, 0)
	}
	return to
}

func (da *Cedar) follow(from int, label byte) int {
	base := da.Array[from].base()
	to := base ^ int(label)
	if base < 0 || da.Array[to].Check < 0 {
		hasChild := false
		if base >= 0 {
			hasChild = (da.Array[base^int(da.Infos[from].Child)].Check == from)
		}
		to = da.popENode(base, label, from)
		da.pushSibling(from, to^int(label), label, hasChild)
	} else if da.Array[to].Check != from {
		to = da.resolve(from, base, label)
	} else if da.Array[to].Check == from {
	} else {
		panic("Cedar: internal error, should not be here")
	}
	return to
}

func (da *Cedar) popBlock(bi int, headIn *int, last bool) {
	if last {
		*headIn = 0
	} else {
		b := &da.Blocks[bi]
		da.Blocks[b.Prev].Next = b.Next
		da.Blocks[b.Next].Prev = b.Prev
		if bi == *headIn {
			*headIn = b.Next
		}
	}
}

func (da *Cedar) pushBlock(bi int, headOut *int, empty bool) {
	b := &da.Blocks[bi]
	if empty {
		*headOut, b.Prev, b.Next = bi, bi, bi
	} else {
		tailOut := &da.Blocks[*headOut].Prev
		b.Prev = *tailOut
		b.Next = *headOut
		*headOut, *tailOut, da.Blocks[*tailOut].Next = bi, bi, bi
	}
}

func (da *Cedar) addBlock() int {
	if da.Size == da.Capacity {
		da.Capacity *= 2

		oldArray := da.Array
		da.Array = make([]Node, da.Capacity)
		copy(da.Array, oldArray)

		oldNinfo := da.Infos
		da.Infos = make([]ninfo, da.Capacity)
		copy(da.Infos, oldNinfo)

		oldBlock := da.Blocks
		da.Blocks = make([]block, da.Capacity>>8)
		copy(da.Blocks, oldBlock)
	}

	da.Blocks[da.Size>>8].init()
	da.Blocks[da.Size>>8].Ehead = da.Size

	da.Array[da.Size] = Node{-(da.Size + 255), -(da.Size + 1)}
	for i := da.Size + 1; i < da.Size+255; i++ {
		da.Array[i] = Node{-(i - 1), -(i + 1)}
	}
	da.Array[da.Size+255] = Node{-(da.Size + 254), -da.Size}

	da.pushBlock(da.Size>>8, &da.bheadO, da.bheadO == 0)
	da.Size += 256
	return da.Size>>8 - 1
}

func (da *Cedar) transferBlock(bi int, headIn, headOut *int) {
	da.popBlock(bi, headIn, bi == da.Blocks[bi].Next)
	da.pushBlock(bi, headOut, *headOut == 0 && da.Blocks[bi].Num != 0)
}

func (da *Cedar) popENode(base int, label byte, from int) int {
	e := base ^ int(label)
	if base < 0 {
		e = da.findPlace()
	}
	bi := e >> 8
	n := &da.Array[e]
	b := &da.Blocks[bi]
	b.Num--
	if b.Num == 0 {
		if bi != 0 {
			da.transferBlock(bi, &da.bheadC, &da.bheadF)
		}
	} else {
		da.Array[-n.Value].Check = n.Check
		da.Array[-n.Check].Value = n.Value
		if e == b.Ehead {
			b.Ehead = -n.Check
		}
		if bi != 0 && b.Num == 1 && b.Trial != da.maxTrial {
			da.transferBlock(bi, &da.bheadO, &da.bheadC)
		}
	}
	n.Value = valueLimit
	n.Check = from
	if base < 0 {
		da.Array[from].Value = -(e ^ int(label)) - 1
	}
	return e
}

func (da *Cedar) pushEnode(e int) {
	bi := e >> 8
	b := &da.Blocks[bi]
	b.Num++
	if b.Num == 1 {
		b.Ehead = e
		da.Array[e] = Node{-e, -e}
		if bi != 0 {
			da.transferBlock(bi, &da.bheadF, &da.bheadC)
		}
	} else {
		prev := b.Ehead
		next := -da.Array[prev].Check
		da.Array[e] = Node{-prev, -next}
		da.Array[prev].Check = -e
		da.Array[next].Value = -e
		if b.Num == 2 || b.Trial == da.maxTrial {
			if bi != 0 {
				da.transferBlock(bi, &da.bheadC, &da.bheadO)
			}
		}
		b.Trial = 0
	}
	if b.reject < da.reject[b.Num] {
		b.reject = da.reject[b.Num]
	}
	da.Infos[e] = ninfo{}
}

// hasChild: wherether the `from` Node has children
func (da *Cedar) pushSibling(from, base int, label byte, hasChild bool) {
	c := &da.Infos[from].Child
	keepOrder := *c == 0
	if da.ordered {
		keepOrder = label > *c
	}
	if hasChild && keepOrder {
		c = &da.Infos[base^int(*c)].Sibling
		for da.ordered && *c != 0 && *c < label {
			c = &da.Infos[base^int(*c)].Sibling
		}
	}
	da.Infos[base^int(label)].Sibling = *c
	*c = label
}

func (da *Cedar) popSibling(from, base int, label byte) {
	c := &da.Infos[from].Child
	for *c != label {
		c = &da.Infos[base^int(*c)].Sibling
	}
	*c = da.Infos[base^int(*c)].Sibling
}

func (da *Cedar) consult(baseN, baseP int, cN, cP byte) bool {
	cN = da.Infos[baseN^int(cN)].Sibling
	cP = da.Infos[baseP^int(cP)].Sibling
	for cN != 0 && cP != 0 {
		cN = da.Infos[baseN^int(cN)].Sibling
		cP = da.Infos[baseP^int(cP)].Sibling
	}
	return cP != 0
}

func (da *Cedar) hasLabel(id int, label byte) bool {
	_, err := da.child(id, label)
	return err == nil
}

func (da *Cedar) child(id int, label byte) (int, error) {
	base := da.Array[id].base()
	cid := base ^ int(label)
	if cid < 0 || cid >= da.Size || da.Array[cid].Check != id {
		return -1, errors.New("cann't find child in Node")
	}
	return cid, nil
}

func (da *Cedar) childs(id int) []ndesc {
	req := []ndesc{}
	base := da.Array[id].base()
	s := da.Infos[id].Child
	if s == 0 && base > 0 {
		s = da.Infos[base].Sibling
	}
	for s != 0 {
		to := base ^ int(s)
		if to < 0 {
			break
		}
		req = append(req, ndesc{ID: to, Label: s})
		s = da.Infos[to].Sibling
	}
	return req
}

func (da *Cedar) setChild(base int, c byte, label byte, flag bool) []byte {
	child := make([]byte, 0, 257)
	if c == 0 {
		child = append(child, c)
		c = da.Infos[base^int(c)].Sibling
	}
	if da.ordered {
		for c != 0 && c <= label {
			child = append(child, c)
			c = da.Infos[base^int(c)].Sibling
		}
	}
	if flag {
		child = append(child, label)
	}
	for c != 0 {
		child = append(child, c)
		c = da.Infos[base^int(c)].Sibling
	}
	return child
}

func (da *Cedar) findPlace() int {
	if da.bheadC != 0 {
		return da.Blocks[da.bheadC].Ehead
	}
	if da.bheadO != 0 {
		return da.Blocks[da.bheadO].Ehead
	}
	return da.addBlock() << 8
}

func (da *Cedar) findPlaces(child []byte) int {
	bi := da.bheadO
	if bi != 0 {
		bz := da.Blocks[da.bheadO].Prev
		nc := len(child)
		for {
			b := &da.Blocks[bi]
			if b.Num >= nc && nc < b.reject {
				for e := b.Ehead; ; {
					base := e ^ int(child[0])
					for i := 0; da.Array[base^int(child[i])].Check < 0; i++ {
						if i == len(child)-1 {
							b.Ehead = e
							return e
						}
					}
					e = -da.Array[e].Check
					if e == b.Ehead {
						break
					}
				}
			}
			b.reject = nc
			if b.reject < da.reject[b.Num] {
				da.reject[b.Num] = b.reject
			}
			bin := b.Next
			b.Trial++
			if b.Trial == da.maxTrial {
				da.transferBlock(bi, &da.bheadO, &da.bheadC)
			}
			if bi == bz {
				break
			}
			bi = bin
		}
	}
	return da.addBlock() << 8
}

func (da *Cedar) resolve(fromN, baseN int, labelN byte) int {
	toPN := baseN ^ int(labelN)
	fromP := da.Array[toPN].Check
	baseP := da.Array[fromP].base()

	flag := da.consult(baseN, baseP, da.Infos[fromN].Child, da.Infos[fromP].Child)
	var children []byte
	if flag {
		children = da.setChild(baseN, da.Infos[fromN].Child, labelN, true)
	} else {
		children = da.setChild(baseP, da.Infos[fromP].Child, 255, false)
	}
	var base int
	if len(children) == 1 {
		base = da.findPlace()
	} else {
		base = da.findPlaces(children)
	}
	base ^= int(children[0])
	var from int
	var nbase int
	if flag {
		from = fromN
		nbase = baseN
	} else {
		from = fromP
		nbase = baseP
	}
	if flag && children[0] == labelN {
		da.Infos[from].Child = labelN
	}
	da.Array[from].Value = -base - 1
	for i := 0; i < len(children); i++ {
		to := da.popENode(base, children[i], from)
		newto := nbase ^ int(children[i])
		if i == len(children)-1 {
			da.Infos[to].Sibling = 0
		} else {
			da.Infos[to].Sibling = children[i+1]
		}
		if flag && newto == toPN { // new Node has no child
			continue
		}
		n := &da.Array[to]
		nn := &da.Array[newto]
		n.Value = nn.Value
		if n.Value < 0 && children[i] != 0 {
			// this Node has children, fix their check
			c := da.Infos[newto].Child
			da.Infos[to].Child = c
			da.Array[n.base()^int(c)].Check = to
			c = da.Infos[n.base()^int(c)].Sibling
			for c != 0 {
				da.Array[n.base()^int(c)].Check = to
				c = da.Infos[n.base()^int(c)].Sibling
			}
		}
		if !flag && newto == fromN { // parent Node moved
			fromN = to
		}
		if !flag && newto == toPN {
			da.pushSibling(fromN, toPN^int(labelN), labelN, true)
			da.Infos[newto].Child = 0
			nn.Value = valueLimit
			nn.Check = fromN
		} else {
			da.pushEnode(newto)
		}
	}
	if flag {
		return base ^ int(labelN)
	}
	return toPN
}

func valueOfRune(r rune) uint16 {
	v := uint32(r)
	if v >= CJKZhMin {
		return uint16(v - CJKZhMin + asciiz + 1)
	}
	return uint16(v)
}

func runeOfValue(v uint16) rune {
	if v >= asciiz {
		return rune(v - 1 - asciiz + CJKZhMin)
	}
	return rune(v)
}

func (da *Cedar) isEnd(id int) bool {
	if da.Infos[id].End {
		return true
	}
	return da.Infos[id].Child == 0
}

func (da *Cedar) toEnd(id int) {
	da.Infos[id].End = true
}

func dumpDFAHeader(out *bytes.Buffer) {
	out.WriteString("digraph DFA {\n")
	out.WriteString("\tNode [color=lightblue2 style=filled]\n")
}

func dumpFinish(out *bytes.Buffer) {
	out.WriteString("}\n")
}

func dumpDFALink(out *bytes.Buffer, fid int, tid int, val uint16, color string) {
	r := runeOfValue(val)
	out.WriteString(fmt.Sprintf("\t\"Node(%d)\" -> \"Node(%d)\" [label=\"(%c)\" color=%s]\n", fid, tid, r, color))
}

func (da *Cedar) dumpTrie(out *bytes.Buffer) {
	end := "END"
	for id := 0; id < da.Size; id++ {
		pid := da.Array[id].Check
		if pid < 0 {
			continue
		}
		pbase := da.Array[pid].base()
		label := pbase ^ id
		if label == 0 {
			label = '0'
		}
		dumpDFALink(out, pid, id, uint16(label), "black")
		if da.isEnd(id) {
			out.WriteString(fmt.Sprintf("\t\"%s\" -> \"END(%d)\"\n", end, id))
			end = fmt.Sprintf("END(%d)", id)
		}
	}
}

// DumpGraph dumps inner data structures for graphviz
func (da *Cedar) DumpGraph(fname string) {
	out := &bytes.Buffer{}
	dumpDFAHeader(out)
	da.dumpTrie(out)
	dumpFinish(out)
	ioutil.WriteFile(fname, out.Bytes(), 0666)
}
