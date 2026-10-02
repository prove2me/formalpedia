-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter10
-- name    : ProofsInTheBook_Chapter10
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:56:59.533294+00:00
-- url     : https://prove2.me/theorems/d4ec8da7-fe7f-4b42-9eec-b8317acd7dab
-- title:
--   Planar off-line incidences and orthogonal projection
-- statement:
--   Points lie in the real Euclidean plane. For points a,b, let $L(a,b)=\operatorname{aff}_{\mathbb R}\{a,b\}$. The perpendicular-distance function is
--   $$\delta(P;a,b)=\inf_{Q\in L(a,b)}\|P-Q\|,$$
--   and the perpendicular foot is the orthogonal projection of P onto this affine subspace. These definitions also apply when a=b, in which case the affine subspace is the singleton containing a.
--
--   For a finite point set S, an off-line incidence consists of $P,a,b\in S$ satisfying $a\ne b$ and $P\notin L(a,b)$. Such an incidence records a specific noncollinear triple in S.
-- source:
--   Mathematical definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter10.lean#L333. Topic: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 11, “Lines in the plane and decompositions of graphs” (https://doi.org/10.1007/978-3-662-57265-8_11). The repository citation specifies the definitions retained here.

import Mathlib

/-!
# Chapter 10: Lines in the plane and decompositions of graphs

From "Proofs from THE BOOK":

**Sylvester-Gallai theorem**: Given a finite set of points in the plane,
not all collinear, there exists a line passing through exactly two of them.

The book's proof (by T. Gallai): Among all pairs (P, ℓ) where P is a point
not on line ℓ (spanned by other points), choose the pair minimizing
dist(P, ℓ). If ℓ contains ≥ 3 points, one can find a closer pair,
contradicting minimality.

The chapter also discusses graph decompositions and the related
theorem about bipartite graphs.
-/

namespace ProofsInTheBook.Chapter10

/-!
### Sylvester-Gallai theorem

The proof by Gallai's extremal argument is a beautiful application of
the well-ordering principle. The formalization requires:
1. A finite point set in ℝ² (or an affine plane)
2. The notion of a line through two points
3. The distance from a point to a line
4. The extremal argument

This geometric result is not yet in Mathlib.
-/












































/-! ## Concrete Euclidean Sylvester–Gallai (Kelly's proof — step 1)

The abstract development above reduces Sylvester–Gallai to the `gallai`
extremal step, supplied as a hypothesis.  To discharge that hypothesis we
work in the concrete plane `EuclideanSpace ℝ (Fin 2)` and follow L. M. Kelly's
metric proof: among all (point, spanned-line) pairs with the point off the
line, a pair of *minimum perpendicular distance* must determine an ordinary
line.

This section builds the metric foundation: the perpendicular distance to the
line through two points, its basic properties, and existence of a minimizing
pair over a finite non-collinear set. -/

section EuclideanSylvesterGallai

open Metric

/-- A point in the Euclidean plane. -/
abbrev EPoint := EuclideanSpace ℝ (Fin 2)

/-- Perpendicular distance from `P` to the line through `a` and `b`
(`= 0` when `a = b`, since the "line" degenerates to a point/`infDist` to it). -/
noncomputable def perpDist (P a b : EPoint) : ℝ :=
  Metric.infDist P (affineSpan ℝ {a, b} : Set EPoint)















/-- An "off-line incidence" of a finite point set `S`: two distinct points
`a, b ∈ S` and a third point `P ∈ S` not on the line they span.  This is the
constructive content of `S` being non-collinear, and the genuine hypothesis of
Sylvester–Gallai. -/
structure OffLineTriple (S : Finset EPoint) where
  P : EPoint
  a : EPoint
  b : EPoint
  hP : P ∈ S
  ha : a ∈ S
  hb : b ∈ S
  hab : a ≠ b
  hoff : P ∉ affineSpan ℝ {a, b}

/-- The incidences of `S` form a finite type: the map to `(P, a, b)` is
injective (the remaining fields are propositions) and lands in the finite set
`S ×ˢ S ×ˢ S`. -/
instance (S : Finset EPoint) : Finite (OffLineTriple S) := by
  apply Finite.of_injective
    (β := {x : EPoint × EPoint × EPoint // x ∈ S ×ˢ S ×ˢ S})
    (fun t => ⟨(t.P, t.a, t.b),
      Finset.mem_product.mpr ⟨t.hP, Finset.mem_product.mpr ⟨t.ha, t.hb⟩⟩⟩)
  rintro ⟨P₁, a₁, b₁, _, _, _, _, _⟩ ⟨P₂, a₂, b₂, _, _, _, _, _⟩ h
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨hP, ha, hb⟩ := h
  subst hP; subst ha; subst hb; rfl

/-- The line through two points, as a nonempty affine subspace instance. -/
instance instNonemptyLinePair (a b : EPoint) :
    Nonempty (affineSpan ℝ {a, b} : AffineSubspace ℝ EPoint) :=
  ⟨a, left_mem_affineSpan_pair ℝ a b⟩

/-- Foot of the perpendicular from `P` to the line through `a` and `b`. -/
noncomputable def foot (P a b : EPoint) : EPoint :=
  EuclideanGeometry.orthogonalProjection (affineSpan ℝ {a, b}) P



































open scoped Classical





end EuclideanSylvesterGallai

end ProofsInTheBook.Chapter10


