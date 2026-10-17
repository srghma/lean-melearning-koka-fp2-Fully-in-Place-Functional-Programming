module

public import RequestProject.Frontend.Util

@[expose] public section

/- ══════════════════ PAPER sec. 4.3, App. A.4 START: Finger trees (PDF pp. 21-22; App. A.4 on pp. 36-38) ══════════════════
   Fully in-place `cons`/`uncons`/`snoc` on finger trees, using explicit reuse tokens. -/

/-!
# Appendix A.4: finger trees

The fully in-place finger trees of Section 4.3 / Appendix A.4 (adapted by the paper
from Claessen's "Finger Trees Explained Anew, and Slightly Simplified"), verbatim.
Constructors are padded with `pad` fields so that every cell has three fields, the
`buffer` keeps reuse credits for later, `bseq` and `tuple4` are unboxed value types, and
`reuse3` is a reuse token.  `bhead` and `head` are ordinary (borrowing, non-`fip`)
functions.  `[KOKA_FIP| ... ]` proves the annotated functions fully in-place.
-/

namespace Examples.FingerTree

open Koka FIP

/-- Appendix A.4: finger trees. -/
def fingertree : FipModule := [KOKA_FIP|
// Adapted from "Finger Trees Explained Anew, and Slightly Simplified (Functional Pearl)", Claessen
import std/num/int32

ref type pad
  Pad

type reuse3
  Reuse3(a : pad, b : pad, c : pad)

type afew<a>
  One(a : a, b : pad, c : pad)
  Two(a : a, b : a, c : pad)
  Three(a : a, b : a, c : a)

type tuple<a>
  Pair(a : a, b : a, c : pad)
  Triple(a : a, b : a, c : a)

type seq<a>
  Empty
  Unit(a : a, b : pad, c : pad)
  More0(l : a, s : seq<tuple<a>>, r : afew<a>)
  More(l : tuple<a>, s : seq<tuple<a>>, r : afew<a>)

type buffer
  BNil
  BCons(next : buffer, b : pad, c : pad)

value type bseq<a>
  BSeq(s : seq<a>, q : buffer)

// Isomorphic to (,,,) but unboxed
value type tuple4<a,b,c,d>
  Tuple4(fst:a,snd:b,thd:c,field4:d)

fun bhead(^bs : bseq<a>) : exn a
  match bs
    BSeq(s, _) -> head(s)

fun head(^s : seq<a>) : exn a
  match s
    Unit(x) -> x
    More0(x, _, _) -> x
    More(Pair(x, _, _), _, _) -> x
    More(Triple(x, _, _), _, _) -> x

fip fun bcons(x : a, u3 : reuse3, bs : bseq<a>) : exn bseq<a>
  val BSeq(s, b) = bs
  val (s', b') = cons(x, u3, s, b)
  BSeq(s', b')

fip fun cons(x : a, u3 : reuse3, s : seq<a>, b : buffer) : exn (seq<a>, buffer)
  match s
    Empty -> (Unit(x, Pad, Pad), b)
    Unit(y, _, _) -> (More0(x, Empty, One(y, Pad, Pad)), b)
    More0(y, q, u) -> (More(Pair(x, y, Pad), q, u), b)
    More(Pair(y, z, _), q, u) ->
      (More(Triple(x, y, z), q, u), BCons(b, Pad, Pad))
    More(Triple(y, z, w), q, u) ->
      val BCons(b', _, _) = b
      val (q', b'') = cons(Pair(z, w, Pad), u3, q, b')
      (More(Pair(x, y, Pad), q', u), b'')

fip fun buncons(bs : bseq<a>) : exn (a, reuse3, bseq<a>)
  val BSeq(s, b) = bs
  val Tuple4(x, u3, s', b') = uncons(s, b)
  (x, u3, BSeq(s', b'))

fip fun uncons(s : seq<a>, b : buffer) : exn tuple4<a, reuse3, seq<a>, buffer>
  match s
    Unit(x, _, _) ->
      Tuple4(x, Reuse3(Pad,Pad,Pad), Empty, b)
    More(Triple(x, y, z), q, u) ->
      val BCons(b', _, _) = b
      Tuple4(x, Reuse3(Pad,Pad,Pad), More(Pair(y, z, Pad), q, u), b')
    More(Pair(x, y, _), q, u) ->
      Tuple4(x, Reuse3(Pad,Pad,Pad), More0(y, q, u), b)
    More0(x, q, u) ->
      val (q', b') = more0(q, u, b)
      Tuple4(x, Reuse3(Pad,Pad,Pad), q', b')

fip fun more0(q : seq<tuple<a>>, u : afew<a>, b : buffer) : exn (seq<a>, buffer)
  match q
    Empty ->
      match u
        One(x, y, z) -> (Unit(x, y, z), b)
        Two(y, z, _) ->
          val BCons(b', _, _) = b
          (More0(y, Empty, One(z, Pad, Pad)), b')
        Three(y, z, w) ->
          val BCons(b', _, _) = b
          (More0(y, Empty, Two(z, w, Pad)), b')
    Unit(p, _, _) ->
      match p
        Pair(x, y, _) -> (More(Pair(x, y, Pad), Empty, u), b)
        Triple(x, y, z) ->
          val BCons(b', _, _) = b
          (More0(x, Unit(Pair(y,z,Pad),Pad,Pad), u), b')
    More0(p, q1, u1) ->
      match p
        Pair(x, y) ->
          val (q1', b') = more0(q1, u1, b)
          (More(Pair(x, y, Pad), q1', u), b')
        Triple(x, y, z) ->
          val BCons(b', _, _) = b
          (More0(x, More0(Pair(y,z,Pad), q1, u1), u), b')
    More(Pair(p, y1), q1, u1) ->
      match p
        Pair(x, y) -> (More(Pair(x, y, Pad), More0(y1, q1, u1), u), b)
        Triple(x, y, z) ->
          val BCons(b', _, _) = b
          (More0(x, More(Pair(Pair(y,z,Pad), y1, Pad), q1, u1), u), b')
    More(Triple(p, y1, z1), q1, u1) ->
      val BCons(b', _, _) = b
      match p
        Pair(x, y) ->
          (More(Pair(x, y, Pad), More(Pair(y1, z1, Pad), q1, u1), u), b')
        Triple(x, y, z) ->
          (More0(x, More(Triple(Pair(y,z,Pad), y1, z1), q1, u1), u), b')

fip fun bsnoc(bs : bseq<a>, u3 : reuse3, x : a) : exn bseq<a>
  val BSeq(s, b) = bs
  val (s', b') = snoc(s, b, u3, x)
  BSeq(s', b')

fip fun snoc(s : seq<a>, b : buffer, u3 : reuse3, x : a) : exn (seq<a>, buffer)
  match s
    Empty -> (Unit(x, Pad, Pad), b)
    Unit(y, _, _) -> (More0(y, Empty, One(x, Pad, Pad)), b)
    More0(u, q, One(y, _, _)) -> (More0(u, q, Two(y, x, Pad)), BCons(b, Pad, Pad))
    More (u, q, One(y, _, _)) -> (More (u, q, Two(y, x, Pad)), BCons(b, Pad, Pad))
    More0(u, q, Two(y, z, _)) -> (More0(u, q, Three(y, z, x)), BCons(b, Pad, Pad))
    More (u, q, Two(y, z, _)) -> (More (u, q, Three(y, z, x)), BCons(b, Pad, Pad))
    More0(u, q, Three(y, z, w)) ->
      val BCons(b', _, _) = b
      val (q', b'') = snoc(q, b', u3, Pair(y, z, Pad))
      (More0(u, q', Two(w, x, Pad)), b'')
    More(u, q, Three(y, z, w)) ->
      val BCons(b', _, _) = b
      val (q', b'') = snoc(q, b', u3, Pair(y, z, Pad))
      (More(u, q', Two(w, x, Pad)), b'')
]

/-- All annotated functions of Appendix A.4 are fully in-place. -/
theorem fingertree_wf : fingertree.sig.Wf := fingertree.wf

/-- The reuse token `Reuse3(Pad, Pad, Pad)`. -/
def u3 {n : Nat} : Val n := .ctor "Reuse3" [.ctor "Pad" [], .ctor "Pad" [], .ctor "Pad" []]

/-- The de Bruijn index `i` as a value. -/
def bv {n : Nat} (i : Nat) (h : i < n := by decide) : Val n := .var (.bvar ⟨i, h⟩)

/-- Push `1, …, 6` on the front of an empty sequence (a `bseq` is unboxed: it is passed
    as the two values `s` and `q`), then pop the first element.  Each `let` binds the two
    components of a sequence, which are the indices `0` and `1` right after it; the last
    two `let`s bind `x, u, s, q` (the popped element, a reuse token and the rest). -/
def pushPop : FIP.Expr 0 :=
  .letIn [false, false]
    (.call "cons" (.ret []) (.ret [.lit 6, u3, .ctor "Empty" [], .ctor "BNil" []])) <|
  .letIn [false, false] (.call "cons" (.ret []) (.ret [.lit 5, u3, bv 0, bv 1])) <|
  .letIn [false, false] (.call "cons" (.ret []) (.ret [.lit 4, u3, bv 0, bv 1])) <|
  .letIn [false, false] (.call "cons" (.ret []) (.ret [.lit 3, u3, bv 0, bv 1])) <|
  .letIn [false, false] (.call "cons" (.ret []) (.ret [.lit 2, u3, bv 0, bv 1])) <|
  .letIn [false, false] (.call "cons" (.ret []) (.ret [.lit 1, u3, bv 0, bv 1])) <|
  .letIn [false, false, false, false] (.call "uncons" (.ret []) (.ret [bv 0, bv 1])) <|
  .letIn [false, false, false, false] (.call "uncons" (.ret []) (.ret [bv 2, bv 3])) <|
  .ret [bv 4, bv 0]

/-- The first two elements popped are `1` and `2`. -/
theorem pushPop_example : pushPop.eval fingertree.sig 10000 = some [.lit 1, .lit 2] := by
  decide +kernel

end Examples.FingerTree

/- ══════════════════ PAPER sec. 4.3, App. A.4 END: Finger trees ══════════════════ -/
