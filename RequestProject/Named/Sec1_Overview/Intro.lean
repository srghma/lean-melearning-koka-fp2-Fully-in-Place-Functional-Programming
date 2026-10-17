module

public import RequestProject.Named.Frontend.Util

@[expose] public section

/-!
# Section 1 of the paper: introductory examples

The fully in-place functions of Section 1 — list reversal, the splay-tree zipper
operations `left`, `lookup`, `zlookup`, `splay`, `splay-leaf`, the borrowing `is-node`
and the `fbip` map `smap` — written verbatim in KokaNamed.  `[NKOKA_FIP| ... ]` compiles them
to the FIPNamed calculus and proves them fully in-place (`FIPNamed.Sig.Wf`).

Two small deviations from the text of the paper: `smap(f, l)` is written `smap(l, f)` to
follow the declared parameter order, and `is-node` is given the `fip fun` keywords.
-/

namespace ExamplesNamed.Intro

open KokaNamed FIPNamed

/-- Section 1 (reverse, splay trees, `smap`). -/
def intro : FipModule := [NKOKA_FIP|
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

fip fun reverse-acc( xs : list<a>, acc : list<a> ) : list<a>
  match! xs
    Cons(x,xx) -> reverse-acc( xx, Cons(x,acc) )
    Nil -> acc

fip fun reverse( xs : list<a> ) : list<a>
  reverse-acc(xs,Nil)

fip fun lookup( t : stree, x : int ) : (bool, stree)
  zlookup(t,x,Root)

fip fun zlookup( t : stree, x : int, ctx : szipper ) : (bool, stree)
  match! t
    Leaf -> (False, splay-leaf(ctx)) // not found, but splay anyway
    Node(l,y,r) ->
      if x < y then zlookup(l,x,NodeL(ctx,y,r)) // go down the left (NodeL reuses Node)
      elif x > y then zlookup(r,x,NodeR(l,y,ctx)) // go down the right (NodeR reuses Node)
      else (True, splay(Top(l,y,r),ctx)) // found it, now splay it to the top

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

fbip fun smap( t : stree, ^f : int -> int) : stree
  match! t
    Node(l,v,r) -> Node(smap(l,f), f(v), smap(r,f))
    Leaf -> Leaf

fip fun is-node( ^t : stree ) : bool
  match t
    Node(_,_,_) -> True
    _ -> False
]

/-- All annotated functions of Section 1 are fully in-place (resp. `fbip`). -/
theorem intro_wf : intro.sig.Wf := intro.wf

/-- A splay tree with keys `1, 2, 3` (right spine). -/
def t123 : Val :=
  .ctor "Node" [atom "Leaf", .lit 1,
    .ctor "Node" [atom "Leaf", .lit 2, .ctor "Node" [atom "Leaf", .lit 3, atom "Leaf"]]]

/-- `reverse([1,2,3,4,5]) = [5,4,3,2,1]`. -/
theorem reverse_example :
    intro.run "reverse" [] [listV [1, 2, 3, 4, 5]] = some [listV [5, 4, 3, 2, 1]] := by
  decide

/-- Looking up `3` finds it and splays it to the root. -/
theorem lookup_example :
    intro.run "lookup" [] [t123, .lit 3] = some [atom "True",
      .ctor "Node" [.ctor "Node" [.ctor "Node" [atom "Leaf", .lit 1, atom "Leaf"], .lit 2,
        atom "Leaf"], .lit 3, atom "Leaf"]] := by
  decide

/-- Looking up `5` does not find it (but splays anyway). -/
theorem lookup_missing :
    (intro.run "lookup" [] [t123, .lit 5]).map (·.head?) = some (some (atom "False")) := by
  decide

end ExamplesNamed.Intro
