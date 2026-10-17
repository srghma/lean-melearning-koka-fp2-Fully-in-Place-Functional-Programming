module

public import RequestProject.Named.Frontend.Util

@[expose] public section

/-!
# Plain KokaNamed functions and the tree map of Section 3

* `[NKOKA| ... ]` compiles ordinary KokaNamed functions (without `fip`), such as the
  list reversal and `palindrome` of Section 1 and the standard `tmap` of Section 3.
* The zipper-based `tmap` of Section 3 (`down`, `app`, `tmap`) is fully in-place.
* `[NKOKA_FIP| ... ]` rejects functions that are not fully in-place, such as
  `palindrome`, which uses its argument twice.
-/

namespace ExamplesNamed.Plain

open KokaNamed FIPNamed

/-- Ordinary (non-`fip`) KokaNamed functions from Sections 1 and 3. -/
def plain : Module := [NKOKA|
fun reverse-acc( xs : list<a>, acc : list<a> ) : list<a>
  match xs
    Cons(x,xx) -> reverse-acc( xx, Cons(x,acc) )
    Nil -> acc

fun reverse( xs : list<a> ) : list<a>
  reverse-acc(xs,Nil)

fun append( xs : list<a>, ys : list<a> ) : list<a>
  match xs
    Cons(x,xx) -> Cons(x, append(xx, ys))
    Nil -> ys

fun palindrome( xs : list<a> ) : list<a>
  append(xs, reverse(xs))

type tree<a>
  Bin(left : tree<a>, right : tree<a>)
  Tip(value : a)

fun tmap(t : tree<a>, ^f : a -> b) : tree<b>
  match! t
    Bin(l,r) ->
      val l' = tmap(l,f)
      val r' = tmap(r,f)
      Bin(l', r')
    Tip(a) -> Tip(f(a))

fun is-pos(x : int) : bool
  x > 0
]

/-- `palindrome([1,2,3]) = [1,2,3,3,2,1]`. -/
theorem palindrome_example :
    plain.run "palindrome" [] [listV [1, 2, 3]] = some [listV [1, 2, 3, 3, 2, 1]] := by
  decide +kernel

/-- Section 3: a fully in-place map over binary trees, using the zipper `tzipper`. -/
def tmapZipper : FipModule := [NKOKA_FIP|
type tree<a>
  Bin(left : tree<a>, right : tree<a>)
  Tip(value : a)

type tzipper<a,b>
  Top
  BinL(up : tzipper<a,b>, right : tree<a>)
  BinR(left : tree<b>, up : tzipper<a,b>)

fip fun down( t : tree<a>, ^f : a -> b, ctx : tzipper<a,b> ) : tree<b>
  match! t
    Bin(l,r) -> down( l, f, BinL(ctx,r) ) // go down the left spine, remember to visit r later
    Tip(x) -> app( Tip(f(x)), f, ctx) // start upwards along the zipper

fip fun app( t : tree<b>, ^f : a -> b, ctx : tzipper<a,b> ) : tree<b>
  match! ctx
    Top -> t // keep going up rebuilding the tree
    BinR(l,up) -> app( Bin(l,t), f, up)
    BinL(up,r) -> down( r, f, BinR(t,up) ) // go down a right side

fip fun tmap( t : tree<a>, ^f : a -> b ) : tree<b>
  down(t,f,Top)

fip fun is-pos( x : int ) : bool
  x > 0
]

/-- The zipper-based `tmap` is fully in-place. -/
theorem tmapZipper_wf : tmapZipper.sig.Wf := tmapZipper.wf

/-- A tree with leaves `1, -2, 3`. -/
def tree123 : Val :=
  .ctor "Bin" [.ctor "Bin" [.ctor "Tip" [.lit 1], .ctor "Tip" [.lit (-2)]], .ctor "Tip" [.lit 3]]

/-- The tree with leaves `True, False, True`. -/
def treeTFT : Val :=
  .ctor "Bin" [.ctor "Bin" [.ctor "Tip" [atom "True"], .ctor "Tip" [atom "False"]],
    .ctor "Tip" [atom "True"]]

/-- Mapping a function over a tree with the zipper-based `tmap` gives the same result as
    the standard recursive `tmap`. -/
theorem tmap_agree :
    tmapZipper.run "tmap" [.fn "is-pos"] [tree123] = some [treeTFT] ∧
    plain.run "tmap" [.fn "is-pos"] [tree123] = some [treeTFT] := by
  decide +kernel

-- `palindrome` is not fully in-place (its argument is used twice), so the quotation
-- below is rejected with an error naming it.
/--
error: KokaNamed: the FIPNamed check fails for [palindrome]
-/
#guard_msgs in
def notFip : FipModule := [NKOKA_FIP|
fip fun reverse-acc( xs : list<a>, acc : list<a> ) : list<a>
  match xs
    Cons(x,xx) -> reverse-acc( xx, Cons(x,acc) )
    Nil -> acc

fip fun reverse( xs : list<a> ) : list<a>
  reverse-acc(xs,Nil)

fip fun append( xs : list<a>, ys : list<a> ) : list<a>
  match xs
    Cons(x,xx) -> Cons(x, append(xx, ys))
    Nil -> ys

fip fun palindrome( xs : list<a> ) : list<a>
  append(xs, reverse(xs))
]

end ExamplesNamed.Plain
