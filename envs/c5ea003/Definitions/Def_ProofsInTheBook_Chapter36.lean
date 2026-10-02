-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter36
-- name    : ProofsInTheBook_Chapter36
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T16:31:35.912917+00:00
-- url     : https://prove2.me/theorems/00a5f9fd-0dc4-44c6-aa57-532904bf88e5
-- title:
--   Abstract triangle attachments and three-color classes
-- statement:
--   For $n\in\mathbb N$, an abstract triangle is an ordered triple $(a,b,c)$ of pairwise distinct elements of $\operatorname{Fin}(n)$. Its undirected edge set is $\{\{a,b\},\{b,c\},\{a,c\}\}$.
--
--   An inductive triangle family begins with one triangle. An attachment adjoins a triangle $T$ with a chosen vertex $v$ such that $v$ occurs in no existing triangle, while the edge of $T$ opposite $v$ is also an edge of some existing triangle. The witness of this construction is `TriangulatedPolygon n S`, where $S$ is the resulting finite set of triangles. No embedding, boundary ordering, visibility relation, or requirement that all $n$ ambient vertices occur is included.
--
--   The colors are red, green and blue. Given two colors, `other_color` returns a different color from both (the unique remaining color when they differ), with specified choices when they coincide. For a finite vertex set $V$, a coloring $c$ and a color $\gamma$, the color class is
--   $$\{v\in V:c(v)=\gamma\}.$$
--   These definitions express the abstract coloring and triangle-hitting objects.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 40, “How to guard a museum”, pp. 281–284 (https://doi.org/10.1007/978-3-662-57265-8_40). Original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter36.lean#L31. This bundle retains the combinatorial definitions and does not define geometric polygon visibility.

import Mathlib

/-!
# Chapter 36: Art galleries

This file proves the combinatorial core of the art gallery theorem: any
abstract polygon triangulation has a 3-coloring, and the smallest color
class gives at most `⌊n / 3⌋` guards meeting every triangle.

Geometry gap audit (2026-05-24): Mathlib has `Geometry.Polygon.Basic`, which
currently provides a vertex-indexed `Polygon`, edge sets, boundary, and
conversion between 3-polygons and affine triangles.  It does not yet provide
the infrastructure needed to state and prove the full geometric art gallery
theorem:

* a definition of a simple polygon as a planar polygonal Jordan curve,
* the polygon interior and the visibility relation from a guard point,
* diagonals lying inside the polygon,
* an ear theorem or equivalent induction step, and
* existence of a triangulation of every simple polygon, together with a proof
  that guards hitting all triangles cover the polygon.

Consequently `chapter36_artgallery_combinatorial` is the closed theorem in
this file.  Extending it to "every simple polygon with `n` vertices is guarded
by `⌊n / 3⌋` vertices" should wait for that geometry layer rather than adding
an unproved triangulation postulate or a placeholder structure here.
-/

namespace ProofsInTheBook.Chapter36

inductive GuardColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open GuardColor

def other_color : GuardColor → GuardColor → GuardColor
  | red, green => blue
  | green, red => blue
  | red, blue => green
  | blue, red => green
  | green, blue => red
  | blue, green => red
  | red, red => green
  | green, green => red
  | blue, blue => red











/-- A triangle on three distinct vertices of `Fin n`. -/
structure AbsTriangle (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c

instance {n : ℕ} : DecidableEq (AbsTriangle n) := by
  intro t1 t2
  obtain ⟨a1, b1, c1, _, _, _⟩ := t1
  obtain ⟨a2, b2, c2, _, _, _⟩ := t2
  if h : a1 = a2 ∧ b1 = b2 ∧ c1 = c2 then
    apply isTrue
    rcases h with ⟨rfl, rfl, rfl⟩
    congr
  else
    apply isFalse
    intro h_eq
    apply h
    injection h_eq with h_a h_b h_c
    exact ⟨h_a, h_b, h_c⟩

/-- The (undirected) edges of an abstract triangle, as a finset of unordered pairs. -/
def AbsTriangle.edges {n : ℕ} (T : AbsTriangle n) : Finset (Sym2 (Fin n)) :=
  {Sym2.mk T.a T.b, Sym2.mk T.b T.c, Sym2.mk T.a T.c}



/-- A combinatorial triangulation: inductively, either a single triangle, or
an existing triangulation with one new triangle glued along exactly one edge. -/
inductive TriangulatedPolygon (n : ℕ) : Finset (AbsTriangle n) → Type
  | single (T : AbsTriangle n) :
      TriangulatedPolygon n {T}
  | glue {S : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S)
      (T : AbsTriangle n)
      (newVertex : Fin n)
      (hT_new : newVertex ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
      (hShared : ∃ T' ∈ S, ∃ e ∈ T.edges, e ∈ T'.edges ∧ newVertex ∉ e)
      (hFresh : ∀ T' ∈ S, newVertex ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))) :
      TriangulatedPolygon n (insert T S)







/-- Vertices of one color class in a finite polygon vertex set. -/
def colorClass {V : Type*} [DecidableEq V] (vertices : Finset V) (color : V → GuardColor)
    (c : GuardColor) : Finset V :=
  vertices.filter fun v => color v = c











/-! ### Concrete combinatorial witnesses

The remaining frontier in this chapter is the geometric existence of a
`TriangulatedPolygon` for an arbitrary simple polygon (needs Mathlib planar
geometry).  The combinatorial layer is complete, so we can exhibit concrete
inductive witnesses on small vertex sets, validating the inductive constructors
and giving downstream callers ready instances to test against. -/







end ProofsInTheBook.Chapter36


