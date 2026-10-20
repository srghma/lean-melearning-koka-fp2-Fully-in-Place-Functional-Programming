module

public import RequestProject.Frontend.Util

@[expose] public section

/-!
# Section 1 of the paper: introductory examples

The fully in-place functions of Section 1 — list reversal, the splay-tree zipper
operations `left`, `lookup`, `zlookup`, `splay`, `splay-leaf`, the borrowing `is-node`
and the `fbip` map `smap` — written verbatim in Koka.  `[KOKA_FIP| ... ]` compiles them
to the FIP calculus and proves them fully in-place (`FIP.Sig.Wf`).

Two small deviations from the text of the paper: `smap(f, l)` is written `smap(l, f)` to
follow the declared parameter order, and `is-node` is given the `fip fun` keywords.
-/

namespace Examples.Intro

open Koka FIP

/-- Section 1 (reverse, splay trees, `smap`). -/
def intro := [KOKA_FIP|
// ==================== PAPER sec. 1.1 START: Zippers and Unboxed Tuples: stree, szipper, left (PDF pp. 2-3) ====================
type stree
  Node(left : stree, value : int, right : stree)
  Leaf

type szipper
  Root
  NodeL(up : szipper, value : int, right : stree)
  NodeR(left : stree, value : int, up : szipper)

type top
  Top(left : stree, value : int, right : stree)

fip fun left(t : stree, ctx : szipper) : (stree,szipper)
  match! t
    Node(l,x,r) -> (l, NodeL(ctx,x,r))
    Leaf -> (Leaf, ctx)

// ==================== PAPER sec. 1.1 END: Zippers and Unboxed Tuples: stree, szipper, left ====================

// ==================== PAPER sec. 1 START: Introduction and Overview: fully in-place reverse with match! (PDF pp. 1-3) ====================
fip fun reverse-acc( xs : list<a>, acc : list<a> ) : list<a>
  match! xs
    Cons(x,xx) -> reverse-acc( xx, Cons(x,acc) )
    Nil -> acc

fip fun reverse( xs : list<a> ) : list<a>
  reverse-acc(xs,Nil)

// ==================== PAPER sec. 1 END: Introduction and Overview: fully in-place reverse with match! ====================

// ==================== PAPER sec. 1.2 START: Splay Tree Lookup and Atoms: lookup, zlookup (PDF pp. 3-4, Fig. 1) ====================
fip fun lookup( t : stree, x : int ) : (bool, stree)
  zlookup(t,x,Root)

fip fun zlookup( t : stree, x : int, ctx : szipper ) : (bool, stree)
  match! t
    Leaf -> (False, splay-leaf(ctx)) // not found, but splay anyway
    Node(l,y,r) ->
      if x < y then zlookup(l,x,NodeL(ctx,y,r)) // go down the left (NodeL reuses Node)
      elif x > y then zlookup(r,x,NodeR(l,y,ctx)) // go down the right (NodeR reuses Node)
      else (True, splay(Top(l,y,r),ctx)) // found it, now splay it to the top

// ==================== PAPER sec. 1.2 END: Splay Tree Lookup and Atoms: lookup, zlookup ====================

// ==================== PAPER sec. 1.2 START: Splay Tree Lookup and Atoms: splay, splay-leaf (PDF pp. 4-5, Fig. 1) ====================
fip fun splay( top : top , ctx : szipper ) : stree
  match! top
    Top(l,x,r) -> match! ctx
      Root -> Node(l,x,r) // zig
      NodeL(Root,y,ry) -> Node(l,x,Node(r,y,ry))
      NodeL(NodeR(lz,z,up),y,ry) -> splay( Top(Node(lz,z,l),x,Node(r,y,ry)), up) // zig-zag
      NodeL(NodeL(up,z,rz),y,ry) -> splay( Top(l,x,Node(r,y,Node(ry,z,rz))), up) // zig-zig
      NodeR(ly,y,Root) -> Node(Node(ly,y,l),x,r)
      NodeR(ly,y,NodeL(up,z,rz)) -> splay( Top(Node(ly,y,l),x,Node(r,z,rz)), up)
      NodeR(ly,y,NodeR(lz,z,up)) -> splay( Top(Node(Node(lz,z,ly),y,l),x,r), up)

fip fun splay-leaf( ctx : szipper ) : stree
  match! ctx
    Root -> Leaf
    NodeL(up,x,r) -> splay(Top(Leaf,x,r),up)
    NodeR(l,x,up) -> splay(Top(l,x,Leaf),up)

// ==================== PAPER sec. 1.2 END: Splay Tree Lookup and Atoms: splay, splay-leaf ====================

// ==================== PAPER sec. 1.3 START: Borrowing and Second-Order Functions: smap, is-node (PDF p. 5) ====================
fbip fun smap( t : stree, ^f : int -> int) : stree
  match! t
    Node(l,v,r) -> Node(smap(l,f), f(v), smap(r,f))
    Leaf -> Leaf

fip fun is-node( ^t : stree ) : bool
  match t
    Node(_,_,_) -> True
    _ -> False
// ==================== PAPER sec. 1.3 END: Borrowing and Second-Order Functions: smap, is-node ====================

// MYTEST
// COMPILE ERROR!
fip fun bad-fact(n : int) : int
  if n <= 0 then 1 else n * bad-fact(n - 1)

fip fun fact(n : int) : int
  // The 'tail' modifier forces the compiler to verify this is a tail call!
  tail fun loop(i : int, acc : int) : int
    if i <= 0 then acc
    else loop(i - 1, i * acc)

  loop(n, 1)

fip fun fact-acc(n : int32, acc : int32) : int32
  if n <= 0.int32 then acc
  else fact-acc(n - 1.int32, n * acc)

fip fun fact(n : int32) : int32
  fact-acc(n, 1.int32)

fip fun fact(n : int) : int
  var acc := 1
  var i   := n
  while { i > 0 }
    acc := acc * i
    i   := i - 1
  acc
]

/- ══════════════════ PAPER sec. 1.3 START (continued): Borrowing and Second-Order Functions: smap, is-node (PDF p. 5) ══════════════════
   The whole Section 1 module passes the FIP/FBIP check. -/

/-- All annotated functions of Section 1 are fully in-place (resp. `fbip`). -/
theorem intro_wf : intro.sig.Wf := intro.wf

/- ══════════════════ PAPER sec. 1.3 END (continued): Borrowing and Second-Order Functions: smap, is-node ══════════════════ -/

/- ══════════════════ PAPER sec. 1 START (continued): Introduction and Overview: fully in-place reverse with match! (PDF pp. 1-3) ══════════════════
   Running the compiled `reverse` on a concrete list. -/

/-- `reverse([1,2,3,4,5]) = [5,4,3,2,1]`. -/
theorem reverse_example :
    intro.eval "reverse" [] [listV [1, 2, 3, 4, 5]] = [listV [5, 4, 3, 2, 1]] := by
  koka_eval

/- ══════════════════ PAPER sec. 1 END (continued): Introduction and Overview: fully in-place reverse with match! ══════════════════ -/

/- ══════════════════ PAPER sec. 1.2 START (continued): Splay Tree Lookup and Atoms: lookup, zlookup (PDF pp. 3-4, Fig. 1) ══════════════════
   Running the compiled `lookup`: a hit splays the key to the root, a miss splays anyway. -/

/-- A splay tree with keys `1, 2, 3` (right spine). -/
def t123 : Val 0 :=
  intro.con "Node" [intro.atom "Leaf", .lit 1,
    intro.con "Node" [intro.atom "Leaf", .lit 2,
      intro.con "Node" [intro.atom "Leaf", .lit 3, intro.atom "Leaf"]]]

/-- Looking up `3` finds it and splays it to the root. -/
theorem lookup_example :
    intro.eval "lookup" [] [t123, .lit 3] = [intro.atom "True",
      intro.con "Node" [intro.con "Node" [intro.con "Node" [intro.atom "Leaf", .lit 1,
        intro.atom "Leaf"], .lit 2, intro.atom "Leaf"], .lit 3, intro.atom "Leaf"]] := by
  koka_eval

/-- Looking up `5` does not find it (but splays anyway). -/
theorem lookup_missing :
    (intro.eval "lookup" [] [t123, .lit 5]).head? = some (intro.atom "False") := by
  koka_eval

/- ══════════════════ PAPER sec. 1.2 END (continued): Splay Tree Lookup and Atoms: lookup, zlookup ══════════════════ -/

end Examples.Intro
