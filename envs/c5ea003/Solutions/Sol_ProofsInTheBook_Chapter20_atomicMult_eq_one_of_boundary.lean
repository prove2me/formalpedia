-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.atomicMult_eq_one_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:50:56.284595+00:00
-- url     : https://prove2.me/submissions/c68e03d8-cca2-4bea-b7cf-6da6fb2b2bf9

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter20 -/
section
set_option autoImplicit true


/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.

Formalization status: this file closes the finite coloring and parity layer.
It defines Monsky's three colors, red-green boundary edges, trichromatic
triangles, proves the local parity identity, proves an abstract Sperner
parity theorem, and derives `chapter20`: a `MonskyCertificate n` yields a
trichromatic triangle.  It also packages Mathlib's local-subring/Zorn
infrastructure into `exists_valuation_extension`, which gives an extension of
any valuation on a field to any field extension; in particular
`exists_real_twoAdic_extension` extends `Rat.padicValuation 2` from `ℚ` to `ℝ`.
Using one chosen extension, the file defines Monsky's coloring on `ℝ²`, proves
the unit-square side color constraints, proves the odd red-green boundary
count for any finite subdivision of the square boundary, identifies that count
with an explicit finite list of unit-square boundary point-edges, constructs
`MonskyCertificate` from finite unordered-edge parity, and proves the valuation
contradiction for a trichromatic triangle of ordinary real area `1 / n` with
`n` odd.

Gap to the full book theorem: the remaining work is geometric triangulation
infrastructure.  One needs a finite real triangulation model for the unit
square and an extraction theorem producing:
1. a finite vertex type `α`, a point map `vertices : α → ℝ × ℝ`, and triangles
   `triangles : Fin n → α × α × α`;
2. four side subdivision lists `bottom right top left : List ℝ`, or equivalently
   the explicit point-edge chain `realTwoAdicSquareBoundaryPointEdgeList`;
3. the boundary-incidence theorem that the odd-multiplicity triangle edges are
   exactly that square boundary chain after mapping boundary points to the
   finite vertex type;
4. the ordinary equal-area fact
   `∀ i, realTriangleArea ... = (1 / n : ℚ)`.
Mathlib has `Analysis.Convex.SimplicialComplex` and `Geometry.Polygon.Basic`,
but not this assembled theorem extracting boundary chains and equal-area facts
from a triangulation of the unit square.
-/

namespace ProofsInTheBook.Chapter20

open IsLocalRing









open MonskyColor

























































































































































































































































/-
Remaining geometric interface: given a hypothetical equal-area triangulation
of the unit square into an odd number of real triangles, one still needs to
extract the finite list of triangle vertices, identify the odd-multiplicity
triangle edges with the explicit square boundary point-edge chain, and express
the equal-area hypothesis as oriented double area `± 2 / n` for each listed
triangle.
-/



















































/-! ### Linear-algebra bridge for `doubleArea`

The signed double-area `doubleArea a b c` is the determinant of the linear map
on `ℝ²` whose standard-basis images are the edge vectors `b - a` and `c - a`.
This rephrasing is the foundation for connecting the chapter's combinatorial
oriented area to Mathlib's `addHaar_image_linearMap` change-of-variables
formula — the route by which a future geometric dissection of the unit square
will deliver the boundary edge-parity (`hboundary`) needed to remove the
remaining `MonskyCertificate` escape.
-/





/-! ### Structural properties of `doubleArea`

Translation invariance, vertex-permutation symmetries, and the collinearity
equivalence — small structural lemmas needed for any future geometric work
on triangle dissections of the unit square (Monsky's remaining frontier).
-/









/-- `doubleArea` is invariant under cyclic permutation of the three vertices. -/
theorem doubleArea_cycle (a b c : ℝ × ℝ) :
    doubleArea b c a = doubleArea a b c := by
  unfold doubleArea
  ring









/-! ### Affine parametrization of the triangle by the filled 2-simplex

The triangle with vertices `a, b, c` is the image, under the affine map
`(s, t) ↦ a + s • (b - a) + t • (c - a)`, of the filled standard 2-simplex
`{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`.  We define the parametrization and
prove the forward containment (image ⊆ convex hull).  Pairing this with the
2-dimensional Lebesgue volume formula for linear-map images is the route to
`volume (convexHull ℝ {a, b, c}) = realTriangleArea a b c`.
-/



@[simp] theorem triangleAffine_zero (a b c : ℝ × ℝ) :
    triangleAffine a b c (0, 0) = a := by
  simp [triangleAffine]

@[simp] theorem triangleAffine_e1 (a b c : ℝ × ℝ) :
    triangleAffine a b c (1, 0) = b := by
  simp [triangleAffine]

@[simp] theorem triangleAffine_e2 (a b c : ℝ × ℝ) :
    triangleAffine a b c (0, 1) = c := by
  simp [triangleAffine]

/-- The parametrization expressed as the standard convex combination of the
three vertices with weights `(1 - s - t, s, t)`. -/
theorem triangleAffine_eq_combo (a b c : ℝ × ℝ) (s t : ℝ) :
    triangleAffine a b c (s, t) = (1 - s - t) • a + s • b + t • c := by
  show a + s • (b - a) + t • (c - a) = (1 - s - t) • a + s • b + t • c
  rw [smul_sub, smul_sub]
  match_scalars <;> ring





/-- Forward direction: every point in the affine image of the filled 2-simplex
is a convex combination of `a, b, c` and therefore lies in their convex hull. -/
theorem triangleAffine_mem_convexHull (a b c : ℝ × ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    triangleAffine a b c (s, t) ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  rw [triangleAffine_eq_combo]
  set S : Set (ℝ × ℝ) := {a, b, c} with hS
  have ha : a ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hb : b ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hc : c ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hconv : Convex ℝ (convexHull ℝ S) := convex_convexHull _ _
  -- Apply Convex.sum_mem with Fin 3, weights (1-s-t, s, t), points (a, b, c).
  have hsum :
      (∑ i : Fin 3, (![(1 - s - t), s, t] : Fin 3 → ℝ) i •
        (![a, b, c] : Fin 3 → ℝ × ℝ) i) ∈ convexHull ℝ S := by
    refine hconv.sum_mem (w := ![(1 - s - t), s, t]) (z := ![a, b, c]) ?_ ?_ ?_
    · intro i _; fin_cases i
      · show (0 : ℝ) ≤ 1 - s - t; linarith
      · show (0 : ℝ) ≤ s; exact hs
      · show (0 : ℝ) ≤ t; exact ht
    · rw [Fin.sum_univ_three]
      show (1 - s - t) + s + t = 1
      ring
    · intro i _; fin_cases i
      · exact ha
      · exact hb
      · exact hc
  -- Reduce the Fin 3 sum to the explicit three-term form.
  simpa [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hsum

/-- The image of the filled 2-simplex under `triangleAffine a b c` is a subset
of the convex hull of `{a, b, c}`. -/
theorem triangleAffine_image_subset_convexHull (a b c : ℝ × ℝ) :
    triangleAffine a b c '' filled2Simplex ⊆
      convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  rintro p ⟨⟨s, t⟩, hst, rfl⟩
  exact triangleAffine_mem_convexHull a b c hst.1 hst.2.1 hst.2.2

/-! ### Brick 1: volume of the filled 2-simplex

The 2-dimensional Lebesgue measure of `filled2Simplex` equals `1/2`.
Direct Fubini route: slice the simplex at fixed `x`, identify the slice
with `Icc 0 (1-x)`, and integrate the linear height. -/









/-! ### Brick 2: convex hull ⊆ triangleAffine image

The reverse inclusion `convexHull ℝ {a, b, c} ⊆ triangleAffine '' filled2Simplex`
combined with `triangleAffine_image_subset_convexHull` gives set equality. -/

/-- The filled standard 2-simplex is convex. -/
theorem convex_filled2Simplex : Convex ℝ filled2Simplex := by
  rintro ⟨s₁, t₁⟩ ⟨hs₁, ht₁, hst₁⟩ ⟨s₂, t₂⟩ ⟨hs₂, ht₂, hst₂⟩ μ ν hμ hν hμν
  refine ⟨?_, ?_, ?_⟩
  · show 0 ≤ μ * s₁ + ν * s₂
    nlinarith
  · show 0 ≤ μ * t₁ + ν * t₂
    nlinarith
  · show μ * s₁ + ν * s₂ + (μ * t₁ + ν * t₂) ≤ 1
    have key : μ * (s₁ + t₁) + ν * (s₂ + t₂) ≤ μ * 1 + ν * 1 := by
      have h1 : μ * (s₁ + t₁) ≤ μ * 1 := by nlinarith
      have h2 : ν * (s₂ + t₂) ≤ ν * 1 := by nlinarith
      linarith
    nlinarith [hμν]

/-- The affine parametrization `triangleAffine a b c` sends a convex combination
of `(s, t)`-parameters to the corresponding convex combination of vertex images. -/
theorem triangleAffine_convex_combo (a b c : ℝ × ℝ) (p q : ℝ × ℝ)
    {μ ν : ℝ} (hμν : μ + ν = 1) :
    triangleAffine a b c (μ • p + ν • q) =
      μ • triangleAffine a b c p + ν • triangleAffine a b c q := by
  obtain ⟨ps, pt⟩ := p
  obtain ⟨qs, qt⟩ := q
  show a + (μ • (ps, pt) + ν • (qs, qt)).1 • (b - a) +
        (μ • (ps, pt) + ν • (qs, qt)).2 • (c - a) =
      μ • (a + ps • (b - a) + pt • (c - a)) +
        ν • (a + qs • (b - a) + qt • (c - a))
  have h1 : ((μ • (ps, pt) + ν • (qs, qt)).1 : ℝ) = μ * ps + ν * qs := by
    simp [Prod.smul_def]
  have h2 : ((μ • (ps, pt) + ν • (qs, qt)).2 : ℝ) = μ * pt + ν * qt := by
    simp [Prod.smul_def]
  rw [h1, h2]
  ext
  · show a.1 + (μ * ps + ν * qs) * (b.1 - a.1) + (μ * pt + ν * qt) * (c.1 - a.1) =
        μ * (a.1 + ps * (b.1 - a.1) + pt * (c.1 - a.1)) +
        ν * (a.1 + qs * (b.1 - a.1) + qt * (c.1 - a.1))
    linear_combination -a.1 * hμν
  · show a.2 + (μ * ps + ν * qs) * (b.2 - a.2) + (μ * pt + ν * qt) * (c.2 - a.2) =
        μ * (a.2 + ps * (b.2 - a.2) + pt * (c.2 - a.2)) +
        ν * (a.2 + qs * (b.2 - a.2) + qt * (c.2 - a.2))
    linear_combination -a.2 * hμν

/-- The image of the filled 2-simplex under `triangleAffine a b c` is convex. -/
theorem convex_triangleAffine_image (a b c : ℝ × ℝ) :
    Convex ℝ (triangleAffine a b c '' filled2Simplex) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ μ ν hμ hν hμν
  refine ⟨μ • p + ν • q, convex_filled2Simplex hp hq hμ hν hμν, ?_⟩
  exact triangleAffine_convex_combo a b c p q hμν

/-- Reverse direction: every point in the convex hull of `{a, b, c}` is of the
form `triangleAffine a b c (s, t)` for some `(s, t)` in the filled 2-simplex. -/
theorem convexHull_subset_triangleAffine_image (a b c : ℝ × ℝ) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆
      triangleAffine a b c '' filled2Simplex := by
  apply convexHull_min ?_ (convex_triangleAffine_image a b c)
  intro p hp
  rcases hp with rfl | hp
  · exact ⟨(0, 0), by simp [filled2Simplex], by simp⟩
  rcases hp with rfl | hp
  · exact ⟨(1, 0), by simp [filled2Simplex], by simp⟩
  · rcases hp with rfl
    exact ⟨(0, 1), by simp [filled2Simplex], by simp⟩

/-- The convex hull of `{a, b, c}` equals the affine image of the filled 2-simplex. -/
theorem convexHull_eq_triangleAffine_image (a b c : ℝ × ℝ) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) = triangleAffine a b c '' filled2Simplex :=
  le_antisymm (convexHull_subset_triangleAffine_image a b c)
    (triangleAffine_image_subset_convexHull a b c)

/-! ### Brick 3: glue to `volume_convexHull_triangle`

The measure-theoretic bridge for Monsky's chapter 20:
`volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (realTriangleArea a b c)`. -/





theorem triangleAffine_eq_add_triangleEdgeMap (a b c st : ℝ × ℝ) :
    triangleAffine a b c st = a + triangleEdgeMap a b c st := by
  show a + st.1 • (b - a) + st.2 • (c - a) = a + (st.1 • (b - a) + st.2 • (c - a))
  rw [add_assoc]









/-! ### Packaged triangulation API

A `RealEqualAreaUnitSquareTriangulation α n` bundles the finite-vertex data
the Monsky frontier theorem
`no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area` consumes.
This is a refactoring layer: every hypothesis the existing theorem takes is
folded into a single named field, so downstream callers only need to construct
one structure instead of supplying twenty-plus arguments. -/





/-! ### Concrete witness: the diagonal split

The unit square can be split into two triangles of area 1/2 each by the main
diagonal — a constructive `RealEqualAreaUnitSquareTriangulation (Fin 4) 2`.
This is also a non-vacuity check on the packaged API: the structure can be
inhabited, just not for odd `n`. -/

namespace RealEqualAreaUnitSquareTriangulation





end RealEqualAreaUnitSquareTriangulation

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Frontier -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 frontier geometry

Auxiliary planar convex-geometry lemmas for the E2 incidence proof.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology

namespace Chapter20E2Frontier



lemma interior_filled2Simplex_subset_strict :
    interior filled2Simplex ⊆
      {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} := by
  intro p hp
  have hpSet : p ∈ filled2Simplex := interior_subset hp
  rcases hpSet with ⟨hx0, hy0, hsum⟩
  have hnhds : filled2Simplex ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hp
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  have hxpos : 0 < p.1 := by
    by_contra hxnot
    have hxle : p.1 ≤ 0 := le_of_not_gt hxnot
    have hx : p.1 = 0 := le_antisymm hxle hx0
    let q : P := (p.1 - ε / 2, p.2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hdist : p.1 - q.1 = ε / 2 := by simp [q]
        rw [show q.1 - p.1 = -(p.1 - q.1) by ring, hdist, abs_neg,
          abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
      · simp [q, hε]
    have hqSet := hball hqball
    have hq0 : 0 ≤ q.1 := hqSet.1
    simp [q, hx] at hq0
    linarith
  have hypos : 0 < p.2 := by
    by_contra hynot
    have hyle : p.2 ≤ 0 := le_of_not_gt hynot
    have hy : p.2 = 0 := le_antisymm hyle hy0
    let q : P := (p.1, p.2 - ε / 2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simp [q, hε]
      · rw [Real.dist_eq]
        have hdist : p.2 - q.2 = ε / 2 := by simp [q]
        rw [show q.2 - p.2 = -(p.2 - q.2) by ring, hdist, abs_neg,
          abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
    have hqSet := hball hqball
    have hq0 : 0 ≤ q.2 := hqSet.2.1
    simp [q, hy] at hq0
    linarith
  have hsumlt : p.1 + p.2 < 1 := by
    by_contra hsnot
    have hsge : 1 ≤ p.1 + p.2 := le_of_not_gt hsnot
    have hs : p.1 + p.2 = 1 := le_antisymm hsum hsge
    let q : P := (p.1 + ε / 2, p.2 + ε / 2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hdist : q.1 - p.1 = ε / 2 := by simp [q]
        rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
      · rw [Real.dist_eq]
        have hdist : q.2 - p.2 = ε / 2 := by simp [q]
        rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
    have hqSet := hball hqball
    have hqsum : q.1 + q.2 ≤ 1 := hqSet.2.2
    simp [q] at hqsum
    linarith
  exact ⟨hxpos, hypos, hsumlt⟩

lemma strict_subset_interior_filled2Simplex :
    {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} ⊆
      interior filled2Simplex := by
  intro p hp
  rcases hp with ⟨hx, hy, hsum⟩
  have hgap : 0 < min (min p.1 p.2) (1 - (p.1 + p.2)) := by
    exact lt_min (lt_min hx hy) (sub_pos.mpr hsum)
  let δ : ℝ := min (min p.1 p.2) (1 - (p.1 + p.2)) / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  refine mem_interior_iff_mem_nhds.mpr ?_
  rw [Metric.mem_nhds_iff]
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
  have hxabs : |q.1 - p.1| < δ := by
    rw [Real.dist_eq] at hq
    exact hq.1
  have hyabs : |q.2 - p.2| < δ := by
    rw [Real.dist_eq] at hq
    exact hq.2
  have hδx : δ < p.1 := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ p.1 :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hδy : δ < p.2 := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ p.2 :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hδsum : 2 * δ < 1 - (p.1 + p.2) := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ 1 - (p.1 + p.2) :=
      min_le_right _ _
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hqx : 0 ≤ q.1 := by
    have hlt : p.1 - q.1 < δ := by
      have hxabs' : |p.1 - q.1| < δ := by
        rwa [abs_sub_comm] at hxabs
      exact lt_of_le_of_lt (le_abs_self _) hxabs'
    linarith
  have hqy : 0 ≤ q.2 := by
    have hlt : p.2 - q.2 < δ := by
      have hyabs' : |p.2 - q.2| < δ := by
        rwa [abs_sub_comm] at hyabs
      exact lt_of_le_of_lt (le_abs_self _) hyabs'
    linarith
  have hqsum : q.1 + q.2 ≤ 1 := by
    have hqxle : q.1 - p.1 < δ := lt_of_le_of_lt (le_abs_self _) hxabs
    have hqyle : q.2 - p.2 < δ := lt_of_le_of_lt (le_abs_self _) hyabs
    linarith
  exact ⟨hqx, hqy, hqsum⟩

lemma interior_filled2Simplex_eq :
    interior filled2Simplex =
      {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} :=
  le_antisymm interior_filled2Simplex_subset_strict strict_subset_interior_filled2Simplex















@[simp]
lemma triangleAffineHomeomorph_apply (a b c : P)
    (hnd : doubleArea a b c ≠ 0) (p : P) :
    triangleAffineHomeomorph a b c hnd p = triangleAffine a b c p := by
  simp [triangleAffineHomeomorph, triangleAffine_eq_add_triangleEdgeMap]

lemma triangleAffineHomeomorph_image_filled2Simplex (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd '' filled2Simplex =
      convexHull ℝ ({a, b, c} : Set P) := by
  rw [convexHull_eq_triangleAffine_image]
  ext p
  simp







theorem interior_convexHull_triangle_of_doubleArea_ne_zero (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    interior (convexHull ℝ ({a, b, c} : Set P)) =
      triangleAffine a b c ''
        {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} := by
  let h := triangleAffineHomeomorph a b c hnd
  have himg := h.image_interior filled2Simplex
  rw [interior_filled2Simplex_eq] at himg
  rw [triangleAffineHomeomorph_image_filled2Simplex a b c hnd] at himg
  rw [← himg]
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    refine ⟨q, hq, ?_⟩
    simpa [h] using hqp
  · rintro ⟨q, hq, hqp⟩
    refine ⟨q, hq, ?_⟩
    simpa [h] using hqp

lemma doubleArea_edge_triangleAffine (a b c : P) (s t : ℝ) :
    doubleArea a b (triangleAffine a b c (s, t)) =
      t * doubleArea a b c := by
  unfold doubleArea triangleAffine
  simp
  ring













lemma exists_openSegment_to_sameSide_mem_interior_convexHull
    (a b c d m : P) (hnd : doubleArea a b c ≠ 0)
    (hm : m ∈ openSegment ℝ a b)
    (hsame : 0 < doubleArea a b d * doubleArea a b c) :
    ∃ x : P,
      x ∈ openSegment ℝ m d ∧
        x ∈ interior (convexHull ℝ ({a, b, c} : Set P)) := by
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨s, hs, hm⟩
  let h := triangleAffineHomeomorph a b c hnd
  let uv : P := h.symm d
  have hd : triangleAffine a b c uv = d := by
    have hd0 : h uv = d := Homeomorph.apply_symm_apply h d
    change triangleAffineHomeomorph a b c hnd uv = d at hd0
    simpa using hd0
  have hm_tri : triangleAffine a b c (s, 0) = (1 - s) • a + s • b := by
    rw [triangleAffine_eq_combo]
    ext <;> simp <;> ring
  have hm' : triangleAffine a b c (s, 0) = m := by
    rw [hm_tri]
    simpa using hm
  have hd_area : doubleArea a b d = uv.2 * doubleArea a b c := by
    rw [← hd]
    obtain ⟨u, v⟩ := uv
    exact doubleArea_edge_triangleAffine a b c u v
  have huv₂_pos : 0 < uv.2 := by
    rw [hd_area] at hsame
    have hsq : 0 < doubleArea a b c * doubleArea a b c := by
      nlinarith [sq_pos_of_ne_zero hnd]
    nlinarith [hsame, hsq]
  let M : ℝ := |uv.1| + |uv.2| + |s| + 1
  have hMpos : 0 < M := by
    dsimp [M]
    nlinarith [abs_nonneg uv.1, abs_nonneg uv.2, abs_nonneg s]
  have hden_pos : 0 < 2 * M := by nlinarith
  let t : ℝ := min (1 / 2) (min (s / (2 * M)) ((1 - s) / (2 * M)))
  have ht_pos : 0 < t := by
    dsimp [t]
    refine lt_min ?_ (lt_min ?_ ?_)
    · norm_num
    · exact div_pos hs.1 hden_pos
    · exact div_pos (sub_pos.mpr hs.2) hden_pos
  have ht_lt_one : t < 1 := by
    dsimp [t]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have ht_le_s : t ≤ s / (2 * M) := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ht_le_one_sub_s : t ≤ (1 - s) / (2 * M) := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have htM_le_s_half : t * M ≤ s / 2 := by
    have h := mul_le_mul_of_nonneg_right ht_le_s (le_of_lt hMpos)
    have hcalc : s / (2 * M) * M = s / 2 := by
      field_simp [ne_of_gt hMpos]
    nlinarith [h, hcalc]
  have htM_le_gap_half : t * M ≤ (1 - s) / 2 := by
    have h := mul_le_mul_of_nonneg_right ht_le_one_sub_s (le_of_lt hMpos)
    have hcalc : (1 - s) / (2 * M) * M = (1 - s) / 2 := by
      field_simp [ne_of_gt hMpos]
    nlinarith [h, hcalc]
  have h_us_lower : -M ≤ uv.1 - s := by
    dsimp [M]
    nlinarith [neg_le_abs uv.1, le_abs_self s, abs_nonneg uv.2]
  have h_uvs_upper : uv.1 + uv.2 - s ≤ M := by
    dsimp [M]
    nlinarith [le_abs_self uv.1, le_abs_self uv.2, neg_le_abs s]
  have hparam₁_pos : 0 < (1 - t) * s + t * uv.1 := by
    have hmul : -t * M ≤ t * (uv.1 - s) := by
      nlinarith [mul_le_mul_of_nonneg_left h_us_lower ht_nonneg]
    nlinarith [hs.1, htM_le_s_half, hmul]
  have hparam₂_pos : 0 < t * uv.2 := by
    positivity
  have hparam_sum_lt :
      (1 - t) * s + t * uv.1 + t * uv.2 < 1 := by
    have hmul : t * (uv.1 + uv.2 - s) ≤ t * M := by
      exact mul_le_mul_of_nonneg_left h_uvs_upper ht_nonneg
    nlinarith [hs.2, htM_le_gap_half, hmul]
  let x : P := (1 - t) • m + t • d
  refine ⟨x, ?_, ?_⟩
  · rw [openSegment_eq_image]
    exact ⟨t, ⟨ht_pos, ht_lt_one⟩, rfl⟩
  · rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd]
    refine ⟨((1 - t) * s + t * uv.1, t * uv.2), ?_, ?_⟩
    · exact ⟨hparam₁_pos, hparam₂_pos, hparam_sum_lt⟩
    · calc
        triangleAffine a b c ((1 - t) * s + t * uv.1, t * uv.2)
            = triangleAffine a b c ((1 - t) • (s, 0) + t • uv) := by
                congr 1
                ext <;> simp [Prod.smul_def] <;> ring
        _ = (1 - t) • triangleAffine a b c (s, 0) +
              t • triangleAffine a b c uv := by
                exact triangleAffine_convex_combo a b c (s, 0) uv (by ring)
        _ = x := by
              simp [x, hm', hd]

lemma exists_common_interior_of_common_sameSide
    (a b c u v w d m : P)
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (hdab : 0 < doubleArea a b d * doubleArea a b c)
    (hduv : 0 < doubleArea u v d * doubleArea u v w) :
    ∃ x : P,
      x ∈ interior (convexHull ℝ ({a, b, c} : Set P)) ∧
        x ∈ interior (convexHull ℝ ({u, v, w} : Set P)) := by
  obtain ⟨x₁, hx₁seg, hx₁int⟩ :=
    exists_openSegment_to_sameSide_mem_interior_convexHull a b c d m habc hmab hdab
  obtain ⟨x₂, hx₂seg, hx₂int⟩ :=
    exists_openSegment_to_sameSide_mem_interior_convexHull u v w d m huvw hmuv hduv
  rw [openSegment_eq_image] at hx₁seg hx₂seg
  rcases hx₁seg with ⟨t₁, ht₁, hx₁⟩
  rcases hx₂seg with ⟨t₂, ht₂, hx₂⟩
  let t : ℝ := min t₁ t₂ / 2
  have htpos : 0 < t := by
    dsimp [t]
    exact half_pos (lt_min ht₁.1 ht₂.1)
  have htt₁ : t < t₁ := by
    dsimp [t]
    have hmin : min t₁ t₂ ≤ t₁ := min_le_left _ _
    nlinarith [ht₁.1, hmin]
  have htt₂ : t < t₂ := by
    dsimp [t]
    have hmin : min t₁ t₂ ≤ t₂ := min_le_right _ _
    nlinarith [ht₂.1, hmin]
  let x : P := (1 - t) • m + t • d
  have hmab_seg : m ∈ segment ℝ a b :=
    openSegment_subset_segment ℝ a b hmab
  have hmuv_seg : m ∈ segment ℝ u v :=
    openSegment_subset_segment ℝ u v hmuv
  have hm₁ : m ∈ convexHull ℝ ({a, b, c} : Set P) := by
    exact segment_subset_convexHull (by simp) (by simp) hmab_seg
  have hm₂ : m ∈ convexHull ℝ ({u, v, w} : Set P) := by
    exact segment_subset_convexHull (by simp) (by simp) hmuv_seg
  have hx_open₁ : x ∈ openSegment ℝ m x₁ := by
    rw [openSegment_eq_image]
    refine ⟨t / t₁, ⟨div_pos htpos ht₁.1, ?_⟩, ?_⟩
    · exact (div_lt_one ht₁.1).mpr htt₁
    · rw [← hx₁]
      ext <;> simp [x] <;> field_simp [ne_of_gt ht₁.1] <;> ring
  have hx_open₂ : x ∈ openSegment ℝ m x₂ := by
    rw [openSegment_eq_image]
    refine ⟨t / t₂, ⟨div_pos htpos ht₂.1, ?_⟩, ?_⟩
    · exact (div_lt_one ht₂.1).mpr htt₂
    · rw [← hx₂]
      ext <;> simp [x] <;> field_simp [ne_of_gt ht₂.1] <;> ring
  refine ⟨x, ?_, ?_⟩
  · exact (convex_convexHull ℝ ({a, b, c} : Set P)).openSegment_self_interior_subset_interior
      hm₁ hx₁int hx_open₁
  · exact (convex_convexHull ℝ ({u, v, w} : Set P)).openSegment_self_interior_subset_interior
      hm₂ hx₂int hx_open₂



theorem frontier_unitSquare :
    frontier (Set.Icc ((0, 0) : P) (1, 1)) =
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)} := by
  have hsquare :
      Set.Icc ((0, 0) : P) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, frontier_prod_eq,
    frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  simp [closure_Icc]
  ext p
  simp [Set.mem_Icc]
  aesop



end Chapter20E2Frontier

export Chapter20E2Frontier
  (
   interior_convexHull_triangle_of_doubleArea_ne_zero
   doubleArea_edge_triangleAffine
   
   
   
   
   
   
   exists_openSegment_to_sameSide_mem_interior_convexHull
   exists_common_interior_of_common_sameSide
   
   frontier_unitSquare)

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Frontier
-/
/- Source module: ProofsInTheBook.Chapter20E2Cover -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 cover lemmas

General connected-cover packaging for the local E2 incidence argument.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology
open Set

namespace Chapter20E2Cover













end Chapter20E2Cover



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Cover
-/
/- Source module: ProofsInTheBook.Chapter20DissectionEngine -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — dissection engine (atomic incidence + reduction to E2)

This file defines a genuine `SquareDissection` (finite triangles, pairwise
disjoint interiors, union the unit square, equal area `1/n`), the atomic-segment
incidence built from it, and reduces Monsky's theorem to the single geometric
incidence fact **E2** (`atomicMult_even_of_interior` / `atomicMult_eq_one_of_boundary`).

The E2 statements are proved here as the main convex-geometry brick
(see `HANDOFF/CH20_E2_SPEC.md`).
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor
open scoped Topology





variable (D : SquareDissection)

























lemma triHull_subset_unitSquare (i : Fin D.n) :
    triHull D i ⊆ unitSquareSet := by
  intro x hx
  have hxUnion :
      x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
    exact Set.mem_iUnion.mpr ⟨i, by simpa [triHull] using hx⟩
  rw [D.cover] at hxUnion
  simpa [unitSquareSet] using hxUnion



open scoped Classical in
lemma mem_sideInteriorChain_iff {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]

open scoped Classical in
lemma sideInteriorChain_nodup (p q : D.vtx) :
    (sideInteriorChain D p q).Nodup := by
  classical
  unfold sideInteriorChain
  have hperm :
      ((Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList.insertionSort
        (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)).Perm
        (Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList :=
    List.perm_insertionSort _ _
  exact (List.Perm.nodup_iff hperm).mpr
    (Finset.nodup_toList (Finset.univ.filter (fun w =>
      OnSide D p q w ∧ w ≠ p ∧ w ≠ q)))

lemma left_not_mem_sideInteriorChain (p q : D.vtx) :
    p ∉ sideInteriorChain D p q := by
  intro hp
  exact (mem_sideInteriorChain_iff (D := D)).mp hp |>.2.1 rfl

lemma right_not_mem_sideInteriorChain (p q : D.vtx) :
    q ∉ sideInteriorChain D p q := by
  intro hq
  exact (mem_sideInteriorChain_iff (D := D)).mp hq |>.2.2 rfl

lemma sideChain_nodup {p q : D.vtx} (hpq : p ≠ q) :
    (p :: sideInteriorChain D p q ++ [q]).Nodup := by
  classical
  rw [List.nodup_append, List.nodup_cons]
  refine ⟨⟨left_not_mem_sideInteriorChain D p q, sideInteriorChain_nodup D p q⟩,
    List.nodup_singleton q, ?_⟩
  intro a ha b hb hab
  rw [List.mem_cons] at ha
  rw [List.mem_singleton] at hb
  subst b
  rcases ha with rfl | ha
  · exact hpq hab
  · exact right_not_mem_sideInteriorChain D p q (hab ▸ ha)

lemma onSide_left (p q : D.vtx) : OnSide D p q p := by
  exact wbtw_self_left (R := ℝ) (D.coord p) (D.coord q)

lemma onSide_right (p q : D.vtx) : OnSide D p q q := by
  exact wbtw_self_right (R := ℝ) (D.coord p) (D.coord q)

lemma sideInteriorChain_onSide {p q w : D.vtx}
    (hw : w ∈ sideInteriorChain D p q) : OnSide D p q w :=
  (mem_sideInteriorChain_iff (D := D)).mp hw |>.1















lemma midpoint_mem_openSegment_of_wbtw_of_ne {P Q A B : ℝ × ℝ}
    (hA : Wbtw ℝ P A Q) (hB : Wbtw ℝ P B Q) (hAB : A ≠ B) :
    midpoint ℝ A B ∈ openSegment ℝ P Q := by
  obtain ⟨ta, hta, rfl⟩ := hA
  obtain ⟨tb, htb, rfl⟩ := hB
  have hta_ne_tb : ta ≠ tb := by
    intro h
    apply hAB
    ext <;> simp [AffineMap.lineMap_apply, h]
  have havg_pos : 0 < (ta + tb) / 2 := by
    by_cases hta0 : ta = 0
    · have htbpos : 0 < tb := by
        have htbne : tb ≠ 0 := by
          intro htb0
          exact hta_ne_tb (by nlinarith)
        exact lt_of_le_of_ne htb.1 (Ne.symm htbne)
      nlinarith
    · have htapos : 0 < ta := lt_of_le_of_ne hta.1 (Ne.symm hta0)
      nlinarith [htb.1]
  have havg_lt : (ta + tb) / 2 < 1 := by
    by_cases hta1 : ta = 1
    · have htblt : tb < 1 := by
        have htbne : tb ≠ 1 := by
          intro htb1
          exact hta_ne_tb (by nlinarith)
        exact lt_of_le_of_ne htb.2 htbne
      nlinarith
    · have htalt : ta < 1 := lt_of_le_of_ne hta.2 hta1
      nlinarith [htb.2]
  rw [openSegment_eq_image]
  refine ⟨(ta + tb) / 2, ⟨havg_pos, havg_lt⟩, ?_⟩
  ext <;> simp [AffineMap.lineMap_apply, midpoint] <;> ring

lemma endpoints_mem_of_mem_consecutiveEdges {α : Type*} {l : List α} {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil =>
      simp [consecutiveEdges] at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges] at h
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons] at h
          rcases h with h | h
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          · have hh := ih h
            simp [hh.1, hh.2]





lemma consecutiveEdges_nodup_of_nodup {α : Type*} [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → (consecutiveEdges l).Nodup
  | [], _ => by simp [consecutiveEdges]
  | [_], _ => by simp [consecutiveEdges]
  | a :: b :: rest, h => by
      rw [consecutiveEdges, List.nodup_cons]
      refine ⟨?_, consecutiveEdges_nodup_of_nodup (List.Nodup.of_cons h)⟩
      intro hmem
      have hend := endpoints_mem_of_mem_consecutiveEdges (l := b :: rest) hmem
      exact List.Nodup.notMem h hend.1

lemma not_diag_mem_consecutiveEdges_of_nodup {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) (a : α) :
    s(a, a) ∉ consecutiveEdges l := by
  induction l with
  | nil =>
      simp [consecutiveEdges]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges]
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons]
          rintro (h | h)
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨hax, hay⟩ | ⟨hay, hax⟩
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
          · exact ih (List.Nodup.of_cons hnd) h

lemma ne_of_mk_mem_consecutiveEdges_of_nodup {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ≠ b := by
  intro hab
  subst b
  exact not_diag_mem_consecutiveEdges_of_nodup hnd a h

lemma onSide_of_mem_sideChain {p q w : D.vtx}
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) : OnSide D p q w := by
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_cons] at hw
    rcases hw with hwp | hw
    · rw [hwp]
      exact onSide_left D p q
    · exact sideInteriorChain_onSide D hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact onSide_right D p q

lemma endpoints_onSide_of_mem_sideAtomicEdges {p q a b : D.vtx}
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    OnSide D p q a ∧ OnSide D p q b := by
  unfold sideAtomicEdges at h
  have hend := endpoints_mem_of_mem_consecutiveEdges h
  exact ⟨onSide_of_mem_sideChain D hend.1, onSide_of_mem_sideChain D hend.2⟩

lemma ne_of_mk_mem_sideAtomicEdges {p q a b : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) : a ≠ b := by
  unfold sideAtomicEdges at h
  exact ne_of_mk_mem_consecutiveEdges_of_nodup (sideChain_nodup D hpq) h





















lemma sideAtomicEdges_nodup {p q : D.vtx} (hpq : p ≠ q) :
    (sideAtomicEdges D p q).Nodup := by
  unfold sideAtomicEdges
  exact consecutiveEdges_nodup_of_nodup (sideChain_nodup D hpq)

lemma tri_v₁_ne_v₂ (i : Fin D.n) : (D.tri i).1 ≠ (D.tri i).2.1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₂_ne_v₃ (i : Fin D.n) : (D.tri i).2.1 ≠ (D.tri i).2.2 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₃_ne_v₁ (i : Fin D.n) : (D.tri i).2.2 ≠ (D.tri i).1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma mem_triAtomicEdges_iff {i : Fin D.n} {e : Sym2 D.vtx} :
    e ∈ triAtomicEdges D i ↔
      e ∈ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.2 (D.tri i).1 := by
  simp [triAtomicEdges, or_assoc]







lemma segment_subset_frontier_unitSquare_of_onSquareBoundary_mk {a b : D.vtx}
    (hbd : OnSquareBoundary D s(a, b)) :
    segment ℝ (D.coord a) (D.coord b) ⊆ frontier unitSquareSet := by
  simpa [OnSquareBoundary, unitSquareSet] using
    (Sym2.fromRel_prop (sym := by
      intro p q h
      rwa [segment_symm]) (a := a) (b := b)).mp hbd





lemma midpoint_mem_openSegment_of_mem_sideAtomicEdges {p q a b : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q) :
    midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord p) (D.coord q) := by
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D h
  have hab : D.coord a ≠ D.coord b := by
    exact fun hcoord => ne_of_mk_mem_sideAtomicEdges D hpq h (D.coord_inj hcoord)
  exact midpoint_mem_openSegment_of_wbtw_of_ne hon.1 hon.2 hab

















lemma doubleArea_product_nonneg_of_segment_subset_frontier_unitSquare
    {A B X Y : ℝ × ℝ}
    (hfront : segment ℝ A B ⊆ frontier unitSquareSet)
    (hX : X ∈ unitSquareSet) (hY : Y ∈ unitSquareSet) :
    0 ≤ doubleArea A B X * doubleArea A B Y := by
  let m := midpoint ℝ A B
  have hAFront :
      A ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
    simpa [unitSquareSet] using hfront (left_mem_segment ℝ A B)
  have hBFront :
      B ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
    simpa [unitSquareSet] using hfront (right_mem_segment ℝ A B)
  have hmFront :
      m ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
    simpa [unitSquareSet, m] using
      hfront (midpoint_mem_segment (𝕜 := ℝ) A B)
  rw [frontier_unitSquare] at hAFront hBFront hmFront
  rcases hAFront with ⟨hA0x, hA1x, hA0y, hA1y, _⟩
  rcases hBFront with ⟨hB0x, hB1x, hB0y, hB1y, _⟩
  rcases hmFront with ⟨_, _, _, _, hmcase⟩
  have hX' : (0 ≤ X.1 ∧ 0 ≤ X.2) ∧ X.1 ≤ 1 ∧ X.2 ≤ 1 := by
    simpa [unitSquareSet, Set.mem_Icc, Prod.le_def] using hX
  have hY' : (0 ≤ Y.1 ∧ 0 ≤ Y.2) ∧ Y.1 ≤ 1 ∧ Y.2 ≤ 1 := by
    simpa [unitSquareSet, Set.mem_Icc, Prod.le_def] using hY
  rcases hmcase with hm0x | hm1x | hm0y | hm1y
  · have hsum : A.1 + B.1 = 0 := by
      have h := hm0x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have hAeq : A.1 = 0 := by nlinarith [hA0x, hB0x, hsum]
    have hBeq : B.1 = 0 := by nlinarith [hA0x, hB0x, hsum]
    unfold doubleArea
    rw [hAeq, hBeq]
    have hnonneg : 0 ≤ X.1 * Y.1 * (B.2 - A.2) ^ 2 :=
      mul_nonneg (mul_nonneg hX'.1.1 hY'.1.1) (sq_nonneg (B.2 - A.2))
    convert hnonneg using 1 <;> ring
  · have hsum : A.1 + B.1 = 2 := by
      have h := hm1x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have hAeq : A.1 = 1 := by nlinarith [hA1x, hB1x, hsum]
    have hBeq : B.1 = 1 := by nlinarith [hA1x, hB1x, hsum]
    unfold doubleArea
    rw [hAeq, hBeq]
    have hXnonneg : 0 ≤ 1 - X.1 := by linarith
    have hYnonneg : 0 ≤ 1 - Y.1 := by linarith
    have hnonneg : 0 ≤ (1 - X.1) * (1 - Y.1) * (B.2 - A.2) ^ 2 :=
      mul_nonneg (mul_nonneg hXnonneg hYnonneg) (sq_nonneg (B.2 - A.2))
    convert hnonneg using 1 <;> ring
  · have hsum : A.2 + B.2 = 0 := by
      have h := hm0y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have hAeq : A.2 = 0 := by nlinarith [hA0y, hB0y, hsum]
    have hBeq : B.2 = 0 := by nlinarith [hA0y, hB0y, hsum]
    unfold doubleArea
    rw [hAeq, hBeq]
    have hnonneg : 0 ≤ X.2 * Y.2 * (B.1 - A.1) ^ 2 :=
      mul_nonneg (mul_nonneg hX'.1.2 hY'.1.2) (sq_nonneg (B.1 - A.1))
    convert hnonneg using 1 <;> ring
  · have hsum : A.2 + B.2 = 2 := by
      have h := hm1y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have hAeq : A.2 = 1 := by nlinarith [hA1y, hB1y, hsum]
    have hBeq : B.2 = 1 := by nlinarith [hA1y, hB1y, hsum]
    unfold doubleArea
    rw [hAeq, hBeq]
    have hXnonneg : 0 ≤ 1 - X.2 := by linarith
    have hYnonneg : 0 ≤ 1 - Y.2 := by linarith
    have hnonneg : 0 ≤ (1 - X.2) * (1 - Y.2) * (B.1 - A.1) ^ 2 :=
      mul_nonneg (mul_nonneg hXnonneg hYnonneg) (sq_nonneg (B.1 - A.1))
    convert hnonneg using 1 <;> ring

lemma linearIndependent_pair_of_doubleArea_ne_zero (a b c : ℝ × ℝ)
    (hnd : doubleArea a b c ≠ 0) :
    LinearIndependent ℝ ![b - a, c - a] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hx : g 0 * (b - a).1 + g 1 * (c - a).1 = 0 := by
    have h := congrArg Prod.fst hsum
    simpa [Fin.sum_univ_two] using h
  have hy : g 0 * (b - a).2 + g 1 * (c - a).2 = 0 := by
    have h := congrArg Prod.snd hsum
    simpa [Fin.sum_univ_two] using h
  have hdet : (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2 ≠ 0 := by
    simpa [doubleArea] using hnd
  fin_cases i
  · have hprod :
        g 0 * ((b - a).1 * (c - a).2 - (c - a).1 * (b - a).2) = 0 := by
      linear_combination (c - a).2 * hx - (c - a).1 * hy
    exact (mul_eq_zero.mp hprod).resolve_right hdet
  · have hprod :
        g 1 * ((b - a).1 * (c - a).2 - (c - a).1 * (b - a).2) = 0 := by
      linear_combination -(b - a).2 * hx + (b - a).1 * hy
    exact (mul_eq_zero.mp hprod).resolve_right hdet

lemma doubleArea_ne_zero_perm₂₁₃ {a b c : ℝ × ℝ}
    (hnd : doubleArea a b c ≠ 0) : doubleArea b a c ≠ 0 := by
  intro h
  apply hnd
  unfold doubleArea at h ⊢
  linear_combination -h

lemma doubleArea_ne_zero_cycle₁ {a b c : ℝ × ℝ}
    (hnd : doubleArea a b c ≠ 0) : doubleArea b c a ≠ 0 := by
  simpa [doubleArea_cycle] using hnd

lemma doubleArea_ne_zero_cycle₂ {a b c : ℝ × ℝ}
    (hnd : doubleArea a b c ≠ 0) : doubleArea c a b ≠ 0 :=
  doubleArea_ne_zero_cycle₁ (doubleArea_ne_zero_cycle₁ hnd)

lemma adjacent_sideAtomicEdges_disjoint {p q r : D.vtx}
    (hnd : doubleArea (D.coord p) (D.coord q) (D.coord r) ≠ 0) :
    (sideAtomicEdges D p q).Disjoint (sideAtomicEdges D q r) := by
  classical
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hpq : p ≠ q := by
        intro h
        apply hnd
        simpa [h, doubleArea]
      have hqr : q ≠ r := by
        intro h
        apply hnd
        simpa [h, doubleArea]
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges D hpq he₁
      have hon₁ := endpoints_onSide_of_mem_sideAtomicEdges D he₁
      have hon₂ := endpoints_onSide_of_mem_sideAtomicEdges D he₂
      have hli :
          LinearIndependent ℝ ![D.coord p - D.coord q, D.coord r - D.coord q] :=
        linearIndependent_pair_of_doubleArea_ne_zero (D.coord q) (D.coord p) (D.coord r)
          (doubleArea_ne_zero_perm₂₁₃ hnd)
      have hinter :
          segment ℝ (D.coord q) (D.coord p) ∩ segment ℝ (D.coord q) (D.coord r) =
            {D.coord q} :=
        segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hli
      have ha_coord : D.coord a = D.coord q := by
        have ha_mem :
            D.coord a ∈
              segment ℝ (D.coord q) (D.coord p) ∩ segment ℝ (D.coord q) (D.coord r) := by
          exact ⟨by simpa [segment_symm] using Wbtw.mem_segment hon₁.1,
            Wbtw.mem_segment hon₂.1⟩
        simpa [hinter] using ha_mem
      have hb_coord : D.coord b = D.coord q := by
        have hb_mem :
            D.coord b ∈
              segment ℝ (D.coord q) (D.coord p) ∩ segment ℝ (D.coord q) (D.coord r) := by
          exact ⟨by simpa [segment_symm] using Wbtw.mem_segment hon₁.2,
            Wbtw.mem_segment hon₂.2⟩
        simpa [hinter] using hb_mem
      exact hne ((D.coord_inj ha_coord).trans (D.coord_inj hb_coord).symm)

lemma triAtomicEdges_nodup (i : Fin D.n) :
    (triAtomicEdges D i).Nodup := by
  classical
  let p := (D.tri i).1
  let q := (D.tri i).2.1
  let r := (D.tri i).2.2
  let l₁ := sideAtomicEdges D p q
  let l₂ := sideAtomicEdges D q r
  let l₃ := sideAtomicEdges D r p
  have hnd : doubleArea (D.coord p) (D.coord q) (D.coord r) ≠ 0 := by
    simpa [p, q, r] using D.nondeg i
  have h₁ : l₁.Nodup := by
    exact sideAtomicEdges_nodup D (by simpa [p, q] using tri_v₁_ne_v₂ D i)
  have h₂ : l₂.Nodup := by
    exact sideAtomicEdges_nodup D (by simpa [q, r] using tri_v₂_ne_v₃ D i)
  have h₃ : l₃.Nodup := by
    exact sideAtomicEdges_nodup D (by simpa [r, p] using tri_v₃_ne_v₁ D i)
  have hd₁₂ : l₁.Disjoint l₂ := by
    exact adjacent_sideAtomicEdges_disjoint D hnd
  have hd₂₃ : l₂.Disjoint l₃ := by
    exact adjacent_sideAtomicEdges_disjoint D (doubleArea_ne_zero_cycle₁ hnd)
  have hd₃₁ : l₃.Disjoint l₁ := by
    exact adjacent_sideAtomicEdges_disjoint D (doubleArea_ne_zero_cycle₂ hnd)
  have hd₁₃ : l₁.Disjoint l₃ := hd₃₁.symm
  have hd₁₂₃ : l₁.Disjoint (l₂ ++ l₃) := by
    rw [List.disjoint_append_right]
    exact ⟨hd₁₂, hd₁₃⟩
  simpa [triAtomicEdges, l₁, l₂, l₃, p, q, r, List.append_assoc] using
    List.Nodup.append h₁ (List.Nodup.append h₂ h₃ hd₂₃) hd₁₂₃



lemma realSign_eq_one_or_neg_one (x : ℝ) :
    realSign x = 1 ∨ realSign x = -1 := by
  by_cases hx : 0 < x <;> simp [realSign, hx]

lemma realSign_eq_imp_mul_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : realSign x = realSign y) :
    0 < x * y := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hsignx : realSign x = -1 := by
      simp [realSign, not_lt_of_ge hxneg.le]
    have hsigny : realSign y = -1 := by
      simpa [hsignx] using hxy.symm
    have hyneg : y < 0 := by
      by_contra hylt
      have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hylt) (Ne.symm hy)
      simp [realSign, hypos] at hsigny
      norm_num at hsigny
    nlinarith
  · have hsignx : realSign x = 1 := by
      simp [realSign, hxpos]
    have hsigny : realSign y = 1 := by
      simpa [hsignx] using hxy.symm
    have hypos : 0 < y := by
      by_contra hylt
      have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hylt) hy
      simp [realSign, not_lt_of_ge hyneg.le] at hsigny
      norm_num at hsigny
    nlinarith

lemma realSign_eq_of_mul_pos {x y : ℝ} (hxy : 0 < x * y) :
    realSign x = realSign y := by
  rcases mul_pos_iff.mp hxy with h | h
  · simp [realSign, h.1, h.2]
  · simp [realSign, not_lt_of_ge h.1.le, not_lt_of_ge h.2.le]

lemma doubleArea_lineMap_lineMap_left (p q r : ℝ × ℝ) (ta tb : ℝ) :
    doubleArea (AffineMap.lineMap p q ta) (AffineMap.lineMap p q tb) r =
      (tb - ta) * doubleArea p q r := by
  unfold doubleArea
  simp [AffineMap.lineMap_apply]
  ring

lemma doubleArea_of_two_wbtw_on_side {p q a b r : ℝ × ℝ}
    (ha : Wbtw ℝ p a q) (hb : Wbtw ℝ p b q) :
    ∃ ta tb : ℝ,
      a = AffineMap.lineMap p q ta ∧
      b = AffineMap.lineMap p q tb ∧
      doubleArea a b r = (tb - ta) * doubleArea p q r := by
  obtain ⟨ta, _hta, haeq⟩ := ha
  obtain ⟨tb, _htb, hbeq⟩ := hb
  refine ⟨ta, tb, haeq.symm, hbeq.symm, ?_⟩
  rw [haeq.symm, hbeq.symm]
  exact doubleArea_lineMap_lineMap_left p q r ta tb

lemma doubleArea_atomicBase_opposite_ne_zero_of_mem_sideAtomicEdges
    {p q r a b : D.vtx}
    (hnd : doubleArea (D.coord p) (D.coord q) (D.coord r) ≠ 0)
    (hmem : s(a, b) ∈ sideAtomicEdges D p q) :
    doubleArea (D.coord a) (D.coord b) (D.coord r) ≠ 0 := by
  have hpq : p ≠ q := by
    intro hpq
    exact hnd (by simp [hpq, doubleArea])
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges D hpq hmem
  have habcoord : D.coord a ≠ D.coord b := fun h => hab (D.coord_inj h)
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D hmem
  obtain ⟨ta, tb, haeq, hbeq, harea⟩ :=
    doubleArea_of_two_wbtw_on_side hon.1 hon.2
  have htab : tb - ta ≠ 0 := by
    intro hzero
    apply habcoord
    rw [haeq, hbeq]
    have htbta : tb = ta := by linarith
    simp [htbta]
  intro hzero
  rw [hzero] at harea
  exact hnd ((mul_eq_zero.mp harea.symm).resolve_left htab)

lemma doubleArea_product_pos_of_mem_sideAtomicEdges
    {p q a b : D.vtx} {x y : ℝ × ℝ}
    (hpq : p ≠ q)
    (hmem : s(a, b) ∈ sideAtomicEdges D p q)
    (hxy : 0 < doubleArea (D.coord a) (D.coord b) x *
      doubleArea (D.coord a) (D.coord b) y) :
    0 < doubleArea (D.coord p) (D.coord q) x *
      doubleArea (D.coord p) (D.coord q) y := by
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges D hpq hmem
  have habcoord : D.coord a ≠ D.coord b := fun h => hab (D.coord_inj h)
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D hmem
  obtain ⟨ta, _hta, haeq⟩ := hon.1
  obtain ⟨tb, _htb, hbeq⟩ := hon.2
  have hxarea :
      doubleArea (D.coord a) (D.coord b) x =
        (tb - ta) * doubleArea (D.coord p) (D.coord q) x := by
    rw [haeq.symm, hbeq.symm]
    exact doubleArea_lineMap_lineMap_left (D.coord p) (D.coord q) x ta tb
  have hyarea :
      doubleArea (D.coord a) (D.coord b) y =
        (tb - ta) * doubleArea (D.coord p) (D.coord q) y := by
    rw [haeq.symm, hbeq.symm]
    exact doubleArea_lineMap_lineMap_left (D.coord p) (D.coord q) y ta tb
  have htab : tb - ta ≠ 0 := by
    intro hzero
    apply habcoord
    rw [haeq.symm, hbeq.symm]
    have htbta : tb = ta := by linarith
    simp [htbta]
  have htab_sq : 0 < (tb - ta) * (tb - ta) := by
    nlinarith [sq_pos_of_ne_zero htab]
  rw [hxarea, hyarea] at hxy
  have hfactor :
      ((tb - ta) * doubleArea (D.coord p) (D.coord q) x) *
        ((tb - ta) * doubleArea (D.coord p) (D.coord q) y) =
      ((tb - ta) * (tb - ta)) *
        (doubleArea (D.coord p) (D.coord q) x *
          doubleArea (D.coord p) (D.coord q) y) := by ring
  rw [hfactor] at hxy
  exact (mul_pos_iff_of_pos_left htab_sq).mp hxy



lemma tri_sideAtomicEdges_disjoint₁₂ (i : Fin D.n) :
    (sideAtomicEdges D (D.tri i).1 (D.tri i).2.1).Disjoint
      (sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2) := by
  exact adjacent_sideAtomicEdges_disjoint D (D.nondeg i)

lemma tri_sideAtomicEdges_disjoint₂₃ (i : Fin D.n) :
    (sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2).Disjoint
      (sideAtomicEdges D (D.tri i).2.2 (D.tri i).1) := by
  exact adjacent_sideAtomicEdges_disjoint D (doubleArea_ne_zero_cycle₁ (D.nondeg i))

lemma tri_sideAtomicEdges_disjoint₃₁ (i : Fin D.n) :
    (sideAtomicEdges D (D.tri i).2.2 (D.tri i).1).Disjoint
      (sideAtomicEdges D (D.tri i).1 (D.tri i).2.1) := by
  exact adjacent_sideAtomicEdges_disjoint D (doubleArea_ne_zero_cycle₂ (D.nondeg i))



lemma exists_incidentSideWitness {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    ∃ W : IncidentSideWitness D i a b, True := by
  rw [mem_triAtomicEdges_iff] at h
  rcases h with h₁ | h₂ | h₃
  · refine ⟨{
      p := (D.tri i).1
      q := (D.tri i).2.1
      r := (D.tri i).2.2
      hmem := h₁
      hHull := by rfl
      hnd := D.nondeg i
      hopp := by simp [incidentOppSign, h₁] }, trivial⟩
  · have hnot₁ :
        s(a, b) ∉ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 := by
      intro h₁
      exact List.disjoint_left.mp (tri_sideAtomicEdges_disjoint₁₂ D i) h₁ h₂
    refine ⟨{
      p := (D.tri i).2.1
      q := (D.tri i).2.2
      r := (D.tri i).1
      hmem := h₂
      hHull := by
        unfold triHull
        congr 1
        ext x
        simp
        tauto
      hnd := doubleArea_ne_zero_cycle₁ (D.nondeg i)
      hopp := by simp [incidentOppSign, hnot₁, h₂] }, trivial⟩
  · have hnot₁ :
        s(a, b) ∉ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 := by
      intro h₁
      exact List.disjoint_left.mp (tri_sideAtomicEdges_disjoint₃₁ D i) h₃ h₁
    have hnot₂ :
        s(a, b) ∉ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 := by
      intro h₂
      exact List.disjoint_left.mp (tri_sideAtomicEdges_disjoint₂₃ D i) h₂ h₃
    refine ⟨{
      p := (D.tri i).2.2
      q := (D.tri i).1
      r := (D.tri i).2.1
      hmem := h₃
      hHull := by
        unfold triHull
        congr 1
        ext x
        simp
        tauto
      hnd := doubleArea_ne_zero_cycle₂ (D.nondeg i)
      hopp := by simp [incidentOppSign, hnot₁, hnot₂] }, trivial⟩

lemma incidentTris_injOn_oppSign {a b : D.vtx} :
    ∀ i k : Fin D.n, i ∈ incidentTris D s(a, b) →
      k ∈ incidentTris D s(a, b) →
      incidentOppSign D a b i = incidentOppSign D a b k → i = k := by
  intro i k hi hk hsign
  by_contra hik_eq
  have hik : i ≠ k := hik_eq
  have hiTri : s(a, b) ∈ triAtomicEdges D i := by
    simpa [incidentTris] using hi
  have hkTri : s(a, b) ∈ triAtomicEdges D k := by
    simpa [incidentTris] using hk
  rcases exists_incidentSideWitness D hiTri with ⟨Wi, _⟩
  rcases exists_incidentSideWitness D hkTri with ⟨Wk, _⟩
  have hsign' :
      realSign (doubleArea (D.coord a) (D.coord b) (D.coord Wi.r)) =
        realSign (doubleArea (D.coord a) (D.coord b) (D.coord Wk.r)) := by
    simpa [Wi.hopp, Wk.hopp] using hsign
  have hABWi_ne :
      doubleArea (D.coord a) (D.coord b) (D.coord Wi.r) ≠ 0 :=
    doubleArea_atomicBase_opposite_ne_zero_of_mem_sideAtomicEdges D Wi.hnd Wi.hmem
  have hABWk_ne :
      doubleArea (D.coord a) (D.coord b) (D.coord Wk.r) ≠ 0 :=
    doubleArea_atomicBase_opposite_ne_zero_of_mem_sideAtomicEdges D Wk.hnd Wk.hmem
  have hABprod :
      0 < doubleArea (D.coord a) (D.coord b) (D.coord Wi.r) *
        doubleArea (D.coord a) (D.coord b) (D.coord Wk.r) :=
    realSign_eq_imp_mul_pos hABWi_ne hABWk_ne hsign'
  have hpq_i : Wi.p ≠ Wi.q := by
    intro hpq
    exact Wi.hnd (by simp [hpq, doubleArea])
  have hpq_k : Wk.p ≠ Wk.q := by
    intro hpq
    exact Wk.hnd (by simp [hpq, doubleArea])
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have hmi :
      m ∈ openSegment ℝ (D.coord Wi.p) (D.coord Wi.q) := by
    simpa [m] using
      midpoint_mem_openSegment_of_mem_sideAtomicEdges D hpq_i Wi.hmem
  have hmk :
      m ∈ openSegment ℝ (D.coord Wk.p) (D.coord Wk.q) := by
    simpa [m] using
      midpoint_mem_openSegment_of_mem_sideAtomicEdges D hpq_k Wk.hmem
  have hsame_i :
      0 < doubleArea (D.coord Wi.p) (D.coord Wi.q) (D.coord Wi.r) *
        doubleArea (D.coord Wi.p) (D.coord Wi.q) (D.coord Wi.r) := by
    nlinarith [sq_pos_of_ne_zero Wi.hnd]
  have hsame_k :
      0 < doubleArea (D.coord Wk.p) (D.coord Wk.q) (D.coord Wi.r) *
        doubleArea (D.coord Wk.p) (D.coord Wk.q) (D.coord Wk.r) :=
    doubleArea_product_pos_of_mem_sideAtomicEdges D hpq_k Wk.hmem hABprod
  obtain ⟨x, hxi, hxk⟩ :=
    exists_common_interior_of_common_sameSide
      (D.coord Wi.p) (D.coord Wi.q) (D.coord Wi.r)
      (D.coord Wk.p) (D.coord Wk.q) (D.coord Wk.r)
      (D.coord Wi.r) m
      Wi.hnd Wk.hnd hmi hmk hsame_i hsame_k
  have hxi' : x ∈ interior (triHull D i) := by
    simpa [Wi.hHull] using hxi
  have hxk' : x ∈ interior (triHull D k) := by
    simpa [Wk.hHull] using hxk
  exact Set.disjoint_left.mp (D.disjoint_int i k hik) hxi' hxk'





































































lemma atomicMult_eq_incidentTris_card (e : Sym2 D.vtx) :
    atomicMult D e = (incidentTris D e).card := by
  classical
  unfold atomicMult incidentTris
  calc
    (∑ i : Fin D.n, (triAtomicEdges D i).count e)
        = ∑ i : Fin D.n, if e ∈ triAtomicEdges D i then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases he : e ∈ triAtomicEdges D i
          · rw [if_pos he]
            exact List.count_eq_one_of_mem (triAtomicEdges_nodup D i) he
          · rw [if_neg he]
            exact List.count_eq_zero_of_not_mem he
    _ = (Finset.univ.filter fun i : Fin D.n => e ∈ triAtomicEdges D i).card := by
          rw [Finset.card_filter]

lemma incidentOppSign_eq_one_or_neg_one (a b : D.vtx) (i : Fin D.n) :
    incidentOppSign D a b i = 1 ∨ incidentOppSign D a b i = -1 := by
  unfold incidentOppSign
  split_ifs <;> exact realSign_eq_one_or_neg_one _



open scoped Classical in
lemma incidentTris_card_eq_image_card (a b : D.vtx) :
    (incidentTris D s(a, b)).card =
      ((incidentTris D s(a, b)).image (incidentOppSign D a b)).card := by
  classical
  exact (Finset.card_image_of_injOn
    (s := incidentTris D s(a, b)) (f := incidentOppSign D a b)
    (by
      intro i hi k hk h
      exact incidentTris_injOn_oppSign D i k hi hk h)).symm



open scoped Classical in
lemma incidentTris_card_eq_one_of_unique_sign {a b : D.vtx} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hmem : σ ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b))
    (huniq : ∀ τ ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b), τ = σ) :
    (incidentTris D s(a, b)).card = 1 := by
  classical
  let I := (incidentTris D s(a, b)).image (incidentOppSign D a b)
  have hI : I = {σ} := by
    ext τ
    constructor
    · intro hτ
      exact Finset.mem_singleton.mpr (huniq τ hτ)
    · intro hτ
      rw [Finset.mem_singleton] at hτ
      simpa [I, hτ] using hmem
  rw [incidentTris_card_eq_image_card D a b]
  change I.card = 1
  rw [hI]
  simp

/-! ### E2 — the geometric incidence core (the single heavy brick) -/





end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20Dissection -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — faithful dissection front end

`Chapter20.lean` proves Monsky's theorem **conditional on** the structure field
`RealEqualAreaUnitSquareTriangulation.hboundary`, which states that an unordered
*full* triangle edge `s(p, r) : Sym2 α` has odd triangle-multiplicity iff it lies
on the square boundary.  That is the *edge-to-edge* (simplicial) special case:
it fails for a genuine dissection in which a triangle side `p–r` is subdivided by
a "T-vertex" `m` belonging to neighbouring triangles, because then `s(p, r)` has
multiplicity `1` (odd) yet is interior.

Monsky's theorem is about **arbitrary** dissections.  The book (Aigner–Ziegler,
Ch. 20, Lemma 2) counts *atomic segments between consecutive vertices* and uses
"every red–green segment in the interior is counted twice".  This file builds
that faithful atomic-segment front end on top of the proved valuation / Sperner
engine in `Chapter20.lean`.

Sub-facts (book Lemma 2):
* **E2** each interior atomic segment lies on exactly two triangle boundaries,
  each boundary atomic segment on exactly one  *(the geometric core)*;
* **E3** on any straight side, the number of red–green atomic segments has the
  parity of `[endpoints are red&green]`, from the ≤2-colors-per-line corollary;
* **E5** the bottom side carries an odd number of red–green atomic segments and
  the other three sides carry none.

This file currently establishes the **≤2-colors-per-line corollary** to Lemma 1,
the foundation E3 rests on.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor





/-! ### E3 — per-side red–green parity (general, from ≤2 colors per line)

Along one straight side of a triangle the dissection vertices form a chain
`a :: middle ++ [b]` lying on a single line, so by the ≤2-colors corollary the
chain uses at most two of the three colors.  In that situation the number of
red–green atomic segments along the chain has exactly the parity of "the two
endpoints `a, b` form a red–green pair".  This upgrades the proved
`listRGTransitionCount_*` side lemmas (which fix the colors per side) to an
arbitrary side of an arbitrary triangle. -/



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20Dissection
-/
/- Source module: ProofsInTheBook.Chapter20Colors -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — collinear-list colour lemmas (E3 plumbing)

The ≤2-colours-per-line corollary (`not_trichromatic_of_collinear`) upgraded
from a single triple to a whole collinear list of points: a list in which every
triple is collinear omits at least one of the three Monsky colours, hence uses at
most two.  Combined with E3 (`odd_listRGTransitionCount_iff_endpoints`) this gives
the per-side red–green parity for an arbitrary subdivided triangle side.

Depends only on `Chapter20Dissection` (brick-1 + E3); independent of the geometric
`SquareDissection` definition, so it is stable while that is under construction.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor







end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20AtomicCount -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — abstract atomic double-count

The list-multiplicity analogue of the full-edge double-count
`sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount`.  Stated abstractly
for a finite family of edge-lists `f : Fin n → List (Sym2 V)`, so the dissection
engine instantiates it with `f := triAtomicEdges D`.  Engine-independent: depends
only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable {V : Type*} [Fintype V] [DecidableEq V]













end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20SideGeom -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — side collinearity

The geometric fact behind the per-side E3 bridge: any three points lying on a
common segment `[P, Q]` are collinear, i.e. their signed double area vanishes.
Used to feed `exists_two_colors_of_collinear_list` for each subdivided triangle
side.  Engine-independent (raw points), instantiated later with vertex coords.
-/

namespace ProofsInTheBook.Chapter20



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20DissectionSperner -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — Sperner→contradiction spine

The engine-independent capstone spine: given a finite family of real triangles
each of area `1/n` (`n` odd) and the parity fact that the summed corner
red–green count is odd, Monsky's coloring forces a rainbow triangle whose area
cannot be `1/n` — contradiction.  This packages
`exists_trichromatic_of_odd_boundary` with
`not_real_triangleArea_eq_one_div_odd_of_trichromatic`, leaving the dissection
engine only to supply the parity hypothesis (`hparity`).

Depends only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20E2Frontier
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Boundary -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — boundary atomic red-green parity

This file contains the boundary half of the atomic E2 bookkeeping: the
red-green atomic edges with odd atomic multiplicity are odd in number.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)















































































































































































































end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20Colors
import ProofsInTheBook.Chapter20AtomicCount
import ProofsInTheBook.Chapter20SideGeom
import ProofsInTheBook.Chapter20DissectionSperner
import ProofsInTheBook.Chapter20E2Boundary
-/
/- Source module: ProofsInTheBook.Chapter20DissectionFinal -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — final assembly

Wires the verified combinatorial layer to the geometric core (E2):
* per-side E3 bridge: along each subdivided triangle side the red-green atomic
  count has the parity of the side's endpoint colours (collinear ⇒ ≤2 colours);
* per-triangle: `listEdgeRGCount (triAtomicEdges i) ≡ triangleLocalRGCount` (mod 2);
* the atomic double-count + E2 turn the summed corner parity into the
  square-boundary atomic parity;
* the boundary organization (odd) + the Sperner spine close the chapter.

`monsky_dissection` is `False`-from-an-odd-equal-area-dissection, conditional only
on the geometric E2 (proved in the engine) and the boundary organization lemma.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)













end ProofsInTheBook.Chapter20

end


set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
open scoped Topology
variable (D : SquareDissection)

theorem solution (e : Sym2 D.vtx)
    (he : IsAtomicEdge D e) (hbd : OnSquareBoundary D e) :
    atomicMult D e = 1 := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      rcases he with ⟨i₀, h₀⟩
      have hi₀ : i₀ ∈ incidentTris D s(a, b) := by
        simpa [incidentTris] using h₀
      let σ := incidentOppSign D a b i₀
      have hσ : σ = 1 ∨ σ = -1 := by
        simpa [σ] using incidentOppSign_eq_one_or_neg_one D a b i₀
      have hσmem :
          σ ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b) := by
        rw [Finset.mem_image]
        exact ⟨i₀, hi₀, rfl⟩
      have hsegFront :
          segment ℝ (D.coord a) (D.coord b) ⊆ frontier unitSquareSet :=
        segment_subset_frontier_unitSquare_of_onSquareBoundary_mk D hbd
      rcases exists_incidentSideWitness D h₀ with ⟨W₀, _⟩
      have hR₀Sq : D.coord W₀.r ∈ unitSquareSet := by
        exact triHull_subset_unitSquare D i₀ (by
          rw [W₀.hHull]
          exact subset_convexHull ℝ
            ({D.coord W₀.p, D.coord W₀.q, D.coord W₀.r} : Set (ℝ × ℝ))
            (by simp))
      have huniq :
          ∀ τ ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b), τ = σ := by
        intro τ hτ
        rw [Finset.mem_image] at hτ
        rcases hτ with ⟨k, hk, rfl⟩
        have hkTri : s(a, b) ∈ triAtomicEdges D k := by
          simpa [incidentTris] using hk
        rcases exists_incidentSideWitness D hkTri with ⟨Wk, _⟩
        have hRkSq : D.coord Wk.r ∈ unitSquareSet := by
          exact triHull_subset_unitSquare D k (by
            rw [Wk.hHull]
            exact subset_convexHull ℝ
              ({D.coord Wk.p, D.coord Wk.q, D.coord Wk.r} : Set (ℝ × ℝ))
              (by simp))
        have hprodNonneg :
            0 ≤ doubleArea (D.coord a) (D.coord b) (D.coord Wk.r) *
              doubleArea (D.coord a) (D.coord b) (D.coord W₀.r) :=
          doubleArea_product_nonneg_of_segment_subset_frontier_unitSquare
            hsegFront hRkSq hR₀Sq
        have hKne :
            doubleArea (D.coord a) (D.coord b) (D.coord Wk.r) ≠ 0 :=
          doubleArea_atomicBase_opposite_ne_zero_of_mem_sideAtomicEdges D Wk.hnd Wk.hmem
        have h₀ne :
            doubleArea (D.coord a) (D.coord b) (D.coord W₀.r) ≠ 0 :=
          doubleArea_atomicBase_opposite_ne_zero_of_mem_sideAtomicEdges D W₀.hnd W₀.hmem
        have hprodPos :
            0 < doubleArea (D.coord a) (D.coord b) (D.coord Wk.r) *
              doubleArea (D.coord a) (D.coord b) (D.coord W₀.r) :=
          lt_of_le_of_ne hprodNonneg (Ne.symm (mul_ne_zero hKne h₀ne))
        have hsign :
            incidentOppSign D a b k = incidentOppSign D a b i₀ := by
          calc
            incidentOppSign D a b k =
                realSign (doubleArea (D.coord a) (D.coord b) (D.coord Wk.r)) := Wk.hopp
            _ = realSign (doubleArea (D.coord a) (D.coord b) (D.coord W₀.r)) :=
                realSign_eq_of_mul_pos hprodPos
            _ = incidentOppSign D a b i₀ := W₀.hopp.symm
        simpa [σ] using hsign
      have hcard : (incidentTris D s(a, b)).card = 1 :=
        incidentTris_card_eq_one_of_unique_sign D hσ hσmem huniq
      rw [atomicMult_eq_incidentTris_card D s(a, b), hcard]
