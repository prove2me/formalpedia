-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter15
-- name    : ProofsInTheBook_Chapter15
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:35:51.650953+00:00
-- url     : https://prove2.me/theorems/8a15ec58-5e09-4981-a7a6-6ef82af41bc5
-- title:
--   Euclidean obtuse triples and perpendicular supporting strips
-- statement:
--   For points $x,y,z\in\mathbb R^d$, set $A(x,y,z)=\langle x-z,y-z\rangle$. An obtuse triple has pairwise distinct vertices and $A(x,y,z)<0$. A finite set has no obtuse angles when this inner product is nonnegative for every triple of distinct points. Define the perpendicular strip determined by distinct $a,b$ by
--   $$0\le\langle b-a,x-a\rangle\le\|b-a\|^2.$$
--   The supporting-strip property requires every point of the finite set to lie in this strip for every distinct pair. The bundle also defines the convex-hull copies, midpoints, separating affine hyperplanes, and affine-span coordinates used in the cardinality argument.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 17, “Every large point set has an obtuse angle”, pp. 111–116 (https://doi.org/10.1007/978-3-662-57265-8_17). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter15.lean#L439. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib

/-!
# Chapter 15: Every large point set has an obtuse angle

The book statement is the Danzer-Grünbaum theorem: any set of more than `2^d`
points in `ℝ^d` contains three points forming an obtuse angle.

Intended Lean theorem: for `points : Finset (EuclideanSpace ℝ (Fin d))`,
`2^d < points.card` should imply that three points of `points` make an obtuse
angle, expressed by a negative inner product.

Formalization status (playbook point 17): status ①. The reduction from the
no-obtuse-angle condition to the antipodal/supporting-strip condition is
formalized below. The Klee packing geometry is formalized through the
half-sized convex-hull copies: they lie inside the original convex hull, have
volume `2^{-d}` times the hull volume, and are pairwise a.e.-disjoint. The
zero ambient-volume case is discharged by reducing to the affine span of the
point set and reapplying the same antipodal bound in that smaller Euclidean
space.

This file intentionally does not contain the old sign-vector pigeonhole theorem:
there is no assumed `sign` map and no assumed injectivity.
-/

namespace ProofsInTheBook.Chapter15

open scoped ENNReal RealInnerProductSpace
open MeasureTheory

noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The inner-product form of the angle at `z` in the triangle `x,z,y`. -/
def AngleInner {d : ℕ} (x y z : Point d) : ℝ :=
  ⟪x - z, y - z⟫

/-- The angle `xzy` is obtuse exactly when this inner product is negative. -/
def ObtuseTriple {d : ℕ} (x y z : Point d) : Prop :=
  AngleInner x y z < 0

/-- No three distinct points of the finite set form an obtuse angle. -/
def NoObtuseAngles {d : ℕ} (points : Finset (Point d)) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, ∀ z ∈ points,
    x ≠ y → x ≠ z → y ≠ z → 0 ≤ AngleInner x y z

/--
For the ordered pair `a,b`, the point `x` lies in the closed strip bounded by
the two hyperplanes through `a` and `b` perpendicular to `b - a`.
-/
def InPerpendicularStrip {d : ℕ} (a b x : Point d) : Prop :=
  0 ≤ ⟪b - a, x - a⟫ ∧ 0 ≤ ⟪a - b, x - b⟫

/--
Every pair of points determines two parallel supporting hyperplanes with all
points in the strip between them: the antipodal-set condition used in the
Danzer-Grünbaum/Klee volume argument.
-/
def HasAntipodalStrips {d : ℕ} (points : Finset (Point d)) : Prop :=
  ∀ a ∈ points, ∀ b ∈ points, a ≠ b → ∀ x ∈ points, InPerpendicularStrip a b x

/-- The half-sized copy of the convex hull used in Klee's packing proof. -/
def KleeCopy {d : ℕ} (points : Finset (Point d)) (p : Point d) : Set (Point d) :=
  (fun x => (2 : ℝ)⁻¹ • (p + x)) '' convexHull ℝ (points : Set (Point d))

/-- The separating hyperplane between the two Klee copies based at `a` and `b`. -/
def KleeMidpoint {d : ℕ} (a b : Point d) : Point d :=
  (2 : ℝ)⁻¹ • (a + b)

def SeparatingHyperplane {d : ℕ} (a b : Point d) : AffineSubspace ℝ (Point d) :=
  AffineSubspace.mk' (KleeMidpoint a b)
    (LinearMap.ker ((innerSL ℝ (b - a) : Point d →L[ℝ] ℝ) : Point d →ₗ[ℝ] ℝ))



































/--
Coordinates on the affine span direction of a point set, with an arbitrary base
point in the affine span. Points outside the affine span are sent to `0`; all
uses below are restricted to the original finite set.
-/
def affineSpanCoord {d : ℕ} (points : Finset (Point d)) (p0 : Point d)
    (hp0A : p0 ∈ affineSpan ℝ (points : Set (Point d)))
    (p : Point d) :
    Point (Module.finrank ℝ (affineSpan ℝ (points : Set (Point d))).direction) := by
  classical
  let A := affineSpan ℝ (points : Set (Point d))
  let W := A.direction
  exact if hp : p ∈ A then
    (stdOrthonormalBasis ℝ W).repr ⟨p - p0, A.vsub_mem_direction hp hp0A⟩
  else 0





















end

end ProofsInTheBook.Chapter15


