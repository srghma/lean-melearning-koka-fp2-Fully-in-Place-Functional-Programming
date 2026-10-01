module

public import RequestProject.Examples.Util

@[expose] public section

/-!
# Appendix A.1: red-black trees

The red-black tree insertion of Section 4.1 / Appendix A.1, with the zipper `accum` and
the functions `is-red`, `ins`, `set-black`, `rebuild`, `insert` and `balance`, written
verbatim in Koka (the listing of the paper, re-indented).  `[KOKA_FIP| ... ]` proves
that all of them are fully in-place; `ins` and `insert` are `fip(1)`: they may allocate
one node (for the new key).
-/

namespace Examples.RedBlack

open Koka FIP

/-- Appendix A.1: red-black tree insertion. -/
def rbtree : FipModule := [KOKA_FIP|
import std/num/int32

type color
  Red
  Black

type tree
  Node(color : color, lchild : tree, key : int32, value : bool, rchild : tree)
  Leaf

fip fun is-red(^t : tree) : bool
  match t
    Node(Red) -> True
    _ -> False

type accum
  Done
  NodeL(color : color, lchild : accum, key : int32, value : bool, rchild : tree)
  NodeR(color : color, lchild : tree, key : int32, value : bool, rchild : accum)

fip(1) fun ins(t : tree, key : int32, v : bool, z : accum) : exn tree
  match t
    Node(c, l, kx, vx, r)
      -> if key < kx then ins(l, key, v, NodeL(c, z, kx, vx, r))
         elif key > kx then ins(r, key, v, NodeR(c, l, kx, vx, z))
         else balance(z, Node(c, l, key, v, r))
    Leaf -> balance(z, Node(Red, Leaf, key, v, Leaf))

fip fun set-black(t : tree) : tree
  match t
    Node(_, l, k, v, r) -> Node(Black, l, k, v, r)
    t -> t

fip fun rebuild(z : accum, t : tree) // Turn the zipper into a tree without rotating
  match z
    NodeR(c, l, k, v, z1) -> rebuild(z1, Node(c, l, k, v, t))
    NodeL(c, z1, k, v, r) -> rebuild(z1, Node(c, t, k, v, r))
    Done -> t

fip(1) fun insert(t : tree, k : int32, v : bool) : <exn> tree
  ins(t, k, v, Done)

fip fun balance( z : accum, t : tree ) : exn tree
  match z
    NodeR(Red, l1, k1, v1, z1) -> match z1
      NodeR(_,l2,k2,v2,z2) -> // black
        if is-red(l2) then balance(z2, Node(Red, l2.set-black, k2, v2, Node(Black, l1, k1, v1, t) ))
        else rebuild(z2, Node(Black, Node(Red,l2,k2,v2,l1), k1, v1, t))
      NodeL(_,z2,k2,v2,r2) -> // black
        if is-red(r2) then balance(z2, Node(Red, Node(Black,l1,k1,v1,t), k2, v2, r2.set-black))
        else match t
          Node(_, l, k, v, r) ->
            rebuild(z2, Node(Black, Node(Red,l1,k1,v1,l), k, v, Node(Red,r,k2,v2,r2)))
      Done -> Node(Black, l1, k1, v1, t)
    NodeL(Red, z1, k1, v1, r1) -> match z1
      NodeL(_,z2,k2,v2,r2) -> // black
        if is-red(r2) then balance(z2, Node(Red, Node(Black, t, k1, v1, r1), k2, v2, r2.set-black ))
        else rebuild(z2, Node(Black, t, k1, v1, Node(Red,r1,k2,v2,r2)))
      NodeR(_,l2,k2,v2,z2) -> // black
        if is-red(l2) then balance(z2, Node(Red, l2.set-black, k2, v2, Node(Black,t,k1,v1,r1) ))
        else match t
          Node(_, l, k, v, r) ->
            rebuild(z2, Node(Black, Node(Red,l2,k2,v2,l), k, v, Node(Red,r,k1,v1,r1)))
      Done -> Node(Black, t, k1, v1, r1)
    z -> rebuild(z, t)
]

/-- All functions of Appendix A.1 are fully in-place. -/
theorem rbtree_wf : rbtree.sig.Wf := rbtree.wf

/-- The keys of a tree of depth at most `n`, in order. -/
def keysN : Nat → Val → List Int
  | n + 1, .ctor "Node" [_, l, .lit k, _, r] => keysN n l ++ k :: keysN n r
  | _, _ => []

/-- The keys of a tree, in order. -/
def keys : Val → List Int := keysN 100

/-- The color of the root. -/
def rootColor : Val → String
  | .ctor "Node" [.ctor c [], _, _, _, _] => c
  | _ => "Leaf"

/-- Inserting `5, 2, 8, 1, 9, 3, 7, 4, 6` into the empty tree. -/
def example_tree : Option (List Val) :=
  rbtree.runFold "insert" (atom "Leaf")
    ([5, 2, 8, 1, 9, 3, 7, 4, 6].map fun k => [.lit k, atom "True"])

/-- The keys of the resulting tree are sorted, and its root is black. -/
theorem insert_example :
    example_tree.map (·.map keys) = some [[1, 2, 3, 4, 5, 6, 7, 8, 9]] ∧
    example_tree.map (·.map rootColor) = some ["Black"] := by
  decide +kernel

end Examples.RedBlack
