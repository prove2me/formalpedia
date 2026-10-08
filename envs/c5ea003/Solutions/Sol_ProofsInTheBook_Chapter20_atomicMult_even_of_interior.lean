-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.atomicMult_even_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:50:58.674733+00:00
-- url     : https://prove2.me/submissions/b3c3bb1d-c608-4ba4-a969-97d41b530755

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

/-- A triple of points in `ℝ²` is collinear iff its signed double-area is zero. -/
theorem doubleArea_eq_zero_iff_collinear (a b c : ℝ × ℝ) :
    doubleArea a b c = 0 ↔
      (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2) := by
  rw [doubleArea, sub_eq_zero]







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

/-- The filled 2-simplex is a closed (and hence measurable) subset of `ℝ × ℝ`. -/
theorem isClosed_filled2Simplex : IsClosed filled2Simplex := by
  have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | p.1 + p.2 ≤ 1} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hclosed :
      IsClosed ({p : ℝ × ℝ | 0 ≤ p.1} ∩
        ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1})) :=
    h1.inter (h2.inter h3)
  exact hclosed







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

lemma mem_segment_std_bottom (p : P) :
    p ∈ segment ℝ ((0, 0) : P) (1, 0) ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro hp
    refine ⟨p.1, ⟨hp.1, hp.2.1⟩, ?_⟩
    ext <;> simp [hp.2.2]

lemma mem_segment_std_diag (p : P) :
    p ∈ segment ℝ ((1, 0) : P) (0, 1) ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ⟨ht.2, ht.1⟩
  · intro hp
    refine ⟨p.2, ⟨hp.2.1, ?_⟩, ?_⟩
    · linarith
    · ext <;> simp
      linarith

lemma mem_segment_std_left (p : P) :
    p ∈ segment ℝ ((0, 1) : P) (0, 0) ↔ p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ⟨ht.2, ht.1⟩
  · intro hp
    refine ⟨1 - p.2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [hp.1]

theorem frontier_filled2Simplex :
    frontier filled2Simplex =
      segment ℝ ((0, 0) : P) (1, 0) ∪
        segment ℝ ((1, 0) : P) (0, 1) ∪
          segment ℝ ((0, 1) : P) (0, 0) := by
  rw [isClosed_filled2Simplex.frontier_eq, interior_filled2Simplex_eq]
  ext p
  constructor
  · rintro ⟨hpFill, hpNotInt⟩
    rcases hpFill with ⟨hx0, hy0, hsum⟩
    simp only [Set.mem_setOf_eq, not_and, not_lt] at hpNotInt
    have hcases : p.1 = 0 ∨ p.2 = 0 ∨ p.1 + p.2 = 1 := by
      by_cases hx : 0 < p.1
      · by_cases hy : 0 < p.2
        · have hge : 1 ≤ p.1 + p.2 := hpNotInt hx hy
          right; right
          exact le_antisymm hsum hge
        · right; left
          exact le_antisymm (le_of_not_gt hy) hy0
      · left
        exact le_antisymm (le_of_not_gt hx) hx0
    rcases hcases with hx | hy | hsumEq
    · right
      rw [mem_segment_std_left]
      exact ⟨hx, hy0, by linarith⟩
    · left; left
      rw [mem_segment_std_bottom]
      exact ⟨hx0, by linarith, hy⟩
    · left; right
      rw [mem_segment_std_diag]
      exact ⟨hx0, hy0, hsumEq⟩
  · intro hp
    rcases hp with hp | hp
    · rcases hp with hp | hp
      · rw [mem_segment_std_bottom] at hp
        refine ⟨⟨hp.1, by linarith, by linarith⟩, ?_⟩
        simp [hp.2.2]
      · rw [mem_segment_std_diag] at hp
        refine ⟨⟨hp.1, hp.2.1, by linarith⟩, ?_⟩
        simp [hp.2.2]
    · rw [mem_segment_std_left] at hp
      refine ⟨⟨by linarith, hp.2.1, by linarith⟩, ?_⟩
      simp [hp.1]



@[simp]
lemma triangleAffineMap_apply (a b c p : P) :
    triangleAffineMap a b c p = triangleAffine a b c p := rfl



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

lemma triangleAffineHomeomorph_image_bottom (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((0, 0) : P) (1, 0) =
      segment ℝ a b := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((0, 0) : P) (1, 0)
        = triangleAffineMap a b c '' segment ℝ ((0, 0) : P) (1, 0) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((0, 0) : P))
          (triangleAffineMap a b c (1, 0)) := by
          rw [image_segment]
    _ = segment ℝ a b := by simp

lemma triangleAffineHomeomorph_image_diag (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((1, 0) : P) (0, 1) =
      segment ℝ b c := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((1, 0) : P) (0, 1)
        = triangleAffineMap a b c '' segment ℝ ((1, 0) : P) (0, 1) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((1, 0) : P))
          (triangleAffineMap a b c (0, 1)) := by
          rw [image_segment]
    _ = segment ℝ b c := by simp

lemma triangleAffineHomeomorph_image_left (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((0, 1) : P) (0, 0) =
      segment ℝ c a := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((0, 1) : P) (0, 0)
        = triangleAffineMap a b c '' segment ℝ ((0, 1) : P) (0, 0) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((0, 1) : P))
          (triangleAffineMap a b c (0, 0)) := by
          rw [image_segment]
    _ = segment ℝ c a := by simp

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



lemma doubleArea_edge_mul_pos_of_mem_interior_convexHull
    (a b c x : P) (hnd : doubleArea a b c ≠ 0)
    (hx : x ∈ interior (convexHull ℝ ({a, b, c} : Set P))) :
    0 < doubleArea a b x * doubleArea a b c := by
  rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd] at hx
  rcases hx with ⟨⟨s, t⟩, hst, rfl⟩
  rw [doubleArea_edge_triangleAffine]
  have ht : 0 < t := hst.2.1
  have hsq : 0 < doubleArea a b c * doubleArea a b c := by
    nlinarith [sq_pos_of_ne_zero hnd]
  nlinarith

lemma doubleArea_eq_zero_of_mem_segment {a b m : P}
    (hm : m ∈ segment ℝ a b) : doubleArea a b m = 0 := by
  rw [segment_eq_image] at hm
  rcases hm with ⟨t, ht, rfl⟩
  unfold doubleArea
  simp [Prod.smul_def]
  ring

lemma doubleArea_direction_combo
    (a b m u v : P) (α β : ℝ)
    (hm : doubleArea a b m = 0) :
    doubleArea a b (m + α • (b - a) + β • (v - u)) =
      β * doubleArea a b (m + (v - u)) := by
  unfold doubleArea at hm ⊢
  simp [Prod.smul_def] at hm ⊢
  ring_nf at hm ⊢
  linear_combination (1 - β) * hm

lemma doubleArea_direction_combo_uv
    (u v m a b : P) (α β : ℝ)
    (hm : doubleArea u v m = 0) :
    doubleArea u v (m + α • (b - a) + β • (v - u)) =
      α * doubleArea u v (m + (b - a)) := by
  unfold doubleArea at hm ⊢
  simp [Prod.smul_def] at hm ⊢
  ring_nf at hm ⊢
  linear_combination (1 - α) * hm

lemma openSegment_edge_to_opposite_subset_interior_convexHull
    (a b c m : P) (hnd : doubleArea a b c ≠ 0)
    (hm : m ∈ openSegment ℝ a b) :
    openSegment ℝ m c ⊆ interior (convexHull ℝ ({a, b, c} : Set P)) := by
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨s, hs, rfl⟩
  intro x hx
  rw [openSegment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd]
  refine ⟨((1 - t) * s, t), ?_, ?_⟩
  · constructor
    · nlinarith [hs.1, ht.2]
    · constructor
      · exact ht.1
      · nlinarith [hs.1, hs.2, ht.1, ht.2]
  · rw [triangleAffine_eq_combo]
    ext <;> simp [smul_add] <;> ring

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

lemma exists_common_sameSide_of_transversal_directions
    (a b c u v w m : P)
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (habuv : doubleArea a b (m + (v - u)) ≠ 0)
    (huvab : doubleArea u v (m + (b - a)) ≠ 0) :
    ∃ d : P,
      0 < doubleArea a b d * doubleArea a b c ∧
        0 < doubleArea u v d * doubleArea u v w := by
  let δab : ℝ := doubleArea a b (m + (v - u))
  let δuv : ℝ := doubleArea u v (m + (b - a))
  let s₁ : ℝ := doubleArea a b c
  let s₂ : ℝ := doubleArea u v w
  let α : ℝ := s₂ * δuv
  let β : ℝ := s₁ * δab
  let d : P := m + α • (b - a) + β • (v - u)
  have hmab0 : doubleArea a b m = 0 :=
    doubleArea_eq_zero_of_mem_segment (openSegment_subset_segment ℝ a b hmab)
  have hmuv0 : doubleArea u v m = 0 :=
    doubleArea_eq_zero_of_mem_segment (openSegment_subset_segment ℝ u v hmuv)
  have hdab_eq : doubleArea a b d = β * δab := by
    simpa [d, δab] using doubleArea_direction_combo a b m u v α β hmab0
  have hduv_eq : doubleArea u v d = α * δuv := by
    simpa [d, δuv] using doubleArea_direction_combo_uv u v m a b α β hmuv0
  refine ⟨d, ?_, ?_⟩
  · rw [hdab_eq]
    have hs₁sq : 0 < s₁ * s₁ := by
      dsimp [s₁]
      nlinarith [sq_pos_of_ne_zero habc]
    have hδabsq : 0 < δab * δab := by
      dsimp [δab]
      nlinarith [sq_pos_of_ne_zero habuv]
    dsimp [β, s₁]
    nlinarith
  · rw [hduv_eq]
    have hs₂sq : 0 < s₂ * s₂ := by
      dsimp [s₂]
      nlinarith [sq_pos_of_ne_zero huvw]
    have hδuvsq : 0 < δuv * δuv := by
      dsimp [δuv]
      nlinarith [sq_pos_of_ne_zero huvab]
    dsimp [α, s₂]
    nlinarith

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

theorem frontier_convexHull_triangle_of_doubleArea_ne_zero (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    frontier (convexHull ℝ ({a, b, c} : Set P)) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  let h := triangleAffineHomeomorph a b c hnd
  have hfront := h.image_frontier filled2Simplex
  rw [frontier_filled2Simplex] at hfront
  rw [triangleAffineHomeomorph_image_filled2Simplex a b c hnd] at hfront
  rw [← hfront]
  rw [Set.image_union, Set.image_union,
    triangleAffineHomeomorph_image_bottom,
    triangleAffineHomeomorph_image_diag,
    triangleAffineHomeomorph_image_left]

end Chapter20E2Frontier

export Chapter20E2Frontier
  (frontier_convexHull_triangle_of_doubleArea_ne_zero
   interior_convexHull_triangle_of_doubleArea_ne_zero
   doubleArea_edge_triangleAffine
   
   doubleArea_edge_mul_pos_of_mem_interior_convexHull
   doubleArea_eq_zero_of_mem_segment
   doubleArea_direction_combo
   doubleArea_direction_combo_uv
   openSegment_edge_to_opposite_subset_interior_convexHull
   exists_openSegment_to_sameSide_mem_interior_convexHull
   exists_common_interior_of_common_sameSide
   exists_common_sameSide_of_transversal_directions
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





lemma doubleArea_affine_combo (a b x y : P) (μ ν : ℝ) (hμν : μ + ν = 1) :
    doubleArea a b (μ • x + ν • y) =
      μ * doubleArea a b x + ν * doubleArea a b y := by
  unfold doubleArea
  simp [Prod.smul_def]
  ring_nf
  linear_combination (b.1 * a.2 - a.1 * b.2) * hμν

lemma convex_signedOpenHalfDisk (a b m : P) {ε σ : ℝ} :
    Convex ℝ (signedOpenHalfDisk a b m ε σ) := by
  intro x hx y hy μ ν hμ hν hμν
  constructor
  · exact (convex_ball m ε) hx.1 hy.1 hμ hν hμν
  · rw [doubleArea_affine_combo a b x y μ ν hμν]
    have hxpos : 0 < σ * doubleArea a b x := hx.2
    have hypos : 0 < σ * doubleArea a b y := hy.2
    have hcombo :
        0 < μ * (σ * doubleArea a b x) + ν * (σ * doubleArea a b y) := by
      by_cases hμ0 : μ = 0
      · have hν1 : ν = 1 := by nlinarith
        nlinarith
      · have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hμ0)
        have hνnonneg : 0 ≤ ν * (σ * doubleArea a b y) := mul_nonneg hν hypos.le
        have hμterm : 0 < μ * (σ * doubleArea a b x) := mul_pos hμpos hxpos
        nlinarith
    convert hcombo using 1
    ring

lemma isPreconnected_signedOpenHalfDisk (a b m : P) {ε σ : ℝ} :
    IsPreconnected (signedOpenHalfDisk a b m ε σ) :=
  (convex_signedOpenHalfDisk a b m).isPreconnected

/-- A nonempty preconnected set covered by finitely many closed sets with
pairwise-disjoint interiors, and avoiding every frontier, lies in one interior. -/
theorem exists_subset_interior_of_preconnected_covered_closed
    {α : Type*} [TopologicalSpace α] {N : ℕ}
    (C : Fin N → Set α) (S : Set α)
    (hclosed : ∀ k, IsClosed (C k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (interior (C k)) (interior (C l)))
    (hSpre : IsPreconnected S) (hSne : S.Nonempty)
    (hcover : S ⊆ ⋃ k, C k)
    (hfront : ∀ k, Disjoint S (frontier (C k))) :
    ∃ k, S ⊆ interior (C k) := by
  classical
  have hcoverInt : S ⊆ ⋃ k, interior (C k) := by
    intro x hxS
    rcases Set.mem_iUnion.mp (hcover hxS) with ⟨k, hxC⟩
    have hxClosure : x ∈ closure (C k) := by
      simpa [(hclosed k).closure_eq] using hxC
    have hxUnion : x ∈ interior (C k) ∪ frontier (C k) := by
      rwa [closure_eq_interior_union_frontier] at hxClosure
    rcases hxUnion with hxInt | hxFront
    · exact Set.mem_iUnion.mpr ⟨k, hxInt⟩
    · exact False.elim (Set.disjoint_left.mp (hfront k) hxS hxFront)
  rcases hSne with ⟨x₀, hx₀S⟩
  rcases Set.mem_iUnion.mp (hcoverInt hx₀S) with ⟨k₀, hx₀k₀⟩
  let U : Set α := interior (C k₀)
  let V : Set α := ⋃ k : {k : Fin N // k ≠ k₀}, interior (C k.1)
  have hUopen : IsOpen U := isOpen_interior
  have hVopen : IsOpen V := isOpen_iUnion fun _ => isOpen_interior
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    rcases Set.mem_iUnion.mp hxV with ⟨k, hxk⟩
    exact Set.disjoint_left.mp (hdisj k₀ k.1 (Ne.symm k.2)) hxU hxk
  have hSUV : S ⊆ U ∪ V := by
    intro x hxS
    rcases Set.mem_iUnion.mp (hcoverInt hxS) with ⟨k, hxk⟩
    by_cases hk : k = k₀
    · exact Or.inl (by simpa [U, hk] using hxk)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩)
  have hSU : (S ∩ U).Nonempty := ⟨x₀, hx₀S, by simpa [U] using hx₀k₀⟩
  exact ⟨k₀, hSpre.subset_left_of_subset_union hUopen hVopen hUV hSUV hSU⟩

end Chapter20E2Cover

export Chapter20E2Cover
  (
   doubleArea_affine_combo
   convex_signedOpenHalfDisk
   isPreconnected_signedOpenHalfDisk
   exists_subset_interior_of_preconnected_covered_closed)

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























lemma triHull_closed (i : Fin D.n) : IsClosed (triHull D i) := by
  unfold triHull
  have hfin :
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)).Finite := by
    simp
  exact hfin.isClosed_convexHull (𝕜 := ℝ)

lemma triHull_subset_unitSquare (i : Fin D.n) :
    triHull D i ⊆ unitSquareSet := by
  intro x hx
  have hxUnion :
      x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
    exact Set.mem_iUnion.mpr ⟨i, by simpa [triHull] using hx⟩
  rw [D.cover] at hxUnion
  simpa [unitSquareSet] using hxUnion

lemma exists_triHull_interior_of_preconnected
    (S : Set (ℝ × ℝ))
    (hSpre : IsPreconnected S) (hSne : S.Nonempty)
    (hcover : S ⊆ unitSquareSet)
    (hfront : ∀ i : Fin D.n, Disjoint S (frontier (triHull D i))) :
    ∃ i : Fin D.n, S ⊆ interior (triHull D i) := by
  refine exists_subset_interior_of_preconnected_covered_closed (C := triHull D) S
    (triHull_closed D) ?_ hSpre hSne ?_ hfront
  · intro i j hij
    simpa [triHull] using D.disjoint_int i j hij
  · intro x hx
    have hxSq : x ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
      simpa [unitSquareSet] using hcover hx
    rw [← D.cover] at hxSq
    simpa [triHull] using hxSq

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

lemma segment_subset_of_onSide {p q a b : D.vtx}
    (ha : OnSide D p q a) (hb : OnSide D p q b) :
    segment ℝ (D.coord a) (D.coord b) ⊆ segment ℝ (D.coord p) (D.coord q) := by
  exact (convex_segment (D.coord p) (D.coord q)).segment_subset
    (Wbtw.mem_segment ha) (Wbtw.mem_segment hb)

lemma sideParam_eq_of_lineMap {p q w : D.vtx} (hpq : p ≠ q) {t : ℝ}
    (hw : D.coord w = AffineMap.lineMap (D.coord p) (D.coord q) t) :
    sideParam D p q w = t := by
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
    have hfst := congrArg Prod.fst hw
    simp [AffineMap.lineMap_apply] at hfst
    field_simp [hx]
    linarith
  · simp [hx]
    have hxeq : (D.coord q).1 = (D.coord p).1 := by exact not_not.mp hx
    have hy : (D.coord q).2 - (D.coord p).2 ≠ 0 := by
      intro hzero
      apply hcoord_ne
      ext
      · exact hxeq
      · linarith
    have hsnd := congrArg Prod.snd hw
    simp [AffineMap.lineMap_apply] at hsnd
    field_simp [hy]
    linarith

lemma sideParam_of_onSide {p q w : D.vtx} (hpq : p ≠ q)
    (hw : OnSide D p q w) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      D.coord w = AffineMap.lineMap (D.coord p) (D.coord q) t ∧
      sideParam D p q w = t := by
  obtain ⟨t, ht, hw⟩ := hw
  exact ⟨t, ht, hw.symm, sideParam_eq_of_lineMap D hpq hw.symm⟩

lemma sideParam_left {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q p = 0 := by
  apply sideParam_eq_of_lineMap D hpq
  ext <;> simp [AffineMap.lineMap_apply]

lemma sideParam_right {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q q = 1 := by
  apply sideParam_eq_of_lineMap D hpq
  ext <;> simp [AffineMap.lineMap_apply]

lemma sideParam_mem_Icc_of_onSide {p q w : D.vtx} (hpq : p ≠ q)
    (hw : OnSide D p q w) :
    sideParam D p q w ∈ Set.Icc (0 : ℝ) 1 := by
  rcases sideParam_of_onSide D hpq hw with ⟨t, ht, _hw, hparam⟩
  simpa [hparam]

lemma sideChain_pairwise {p q : D.vtx} (hpq : p ≠ q) :
    (p :: sideInteriorChain D p q ++ [q]).Pairwise
      (fun x y => sideParam D p q x ≤ sideParam D p q y) := by
  classical
  have hchain :
      (sideInteriorChain D p q).Pairwise
        (fun x y => sideParam D p q x ≤ sideParam D p q y) := by
    unfold sideInteriorChain
    exact List.pairwise_insertionSort _ _
  have hpchain :
      (p :: sideInteriorChain D p q).Pairwise
        (fun x y => sideParam D p q x ≤ sideParam D p q y) := by
    rw [List.pairwise_cons]
    constructor
    · intro y hy
      have hp0 := sideParam_left D hpq
      have hyon : OnSide D p q y :=
        (mem_sideInteriorChain_iff (D := D)).mp hy |>.1
      have hyIcc := sideParam_mem_Icc_of_onSide D hpq hyon
      rw [hp0]
      exact hyIcc.1
    · exact hchain
  rw [List.pairwise_append]
  refine ⟨hpchain, by simp, ?_⟩
  intro x hx y hy
  rw [List.mem_singleton] at hy
  subst y
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · rw [sideParam_left D hpq, sideParam_right D hpq]
    norm_num
  · have hxIcc : sideParam D p q x ∈ Set.Icc (0 : ℝ) 1 := by
      have hxon : OnSide D p q x :=
        (mem_sideInteriorChain_iff (D := D)).mp hx |>.1
      exact sideParam_mem_Icc_of_onSide D hpq hxon
    rw [sideParam_right D hpq]
    exact hxIcc.2

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

lemma not_key_between_of_mem_consecutiveEdges_pairwise
    {α : Type*} {f : α → ℝ} :
    ∀ {l : List α} {a b z : α},
      l.Pairwise (fun x y => f x ≤ f y) →
      s(a, b) ∈ consecutiveEdges l →
      z ∈ l →
      ¬ ((f a < f z ∧ f z < f b) ∨ (f b < f z ∧ f z < f a))
  | [], a, b, z, hpair, hmem, hz => by
      simp [consecutiveEdges] at hmem
  | [_x], a, b, z, hpair, hmem, hz => by
      simp [consecutiveEdges] at hmem
  | x :: y :: ys, a, b, z, hpair, hmem, hz => by
      rw [consecutiveEdges, List.mem_cons] at hmem
      rw [List.mem_cons] at hz
      have hpair_tail : (y :: ys).Pairwise (fun x y => f x ≤ f y) :=
        (List.pairwise_cons.mp hpair).2
      have hx_le_tail : ∀ t ∈ y :: ys, f x ≤ f t :=
        (List.pairwise_cons.mp hpair).1
      rcases hmem with hhead | htail
      · rw [Sym2.eq_iff] at hhead
        rcases hhead with ⟨hax, hby⟩ | ⟨hay, hbx⟩
        · have hxy : f x ≤ f y := hx_le_tail y (by simp)
          subst a
          subst b
          intro hbetween
          rcases hz with rfl | hz
          · rcases hbetween with hbetween | hbetween <;> linarith
          · rw [List.mem_cons] at hz
            rcases hz with rfl | hzys
            · rcases hbetween with hbetween | hbetween <;> linarith
            · have hy_le_z : f y ≤ f z :=
                (List.pairwise_cons.mp hpair_tail).1 z hzys
              have hx_le_z : f x ≤ f z := hx_le_tail z (by simp [hzys])
              rcases hbetween with hbetween | hbetween <;> linarith
        · have hxy : f x ≤ f y := hx_le_tail y (by simp)
          subst a
          subst b
          intro hbetween
          rcases hz with rfl | hz
          · rcases hbetween with hbetween | hbetween <;> linarith
          · rw [List.mem_cons] at hz
            rcases hz with rfl | hzys
            · rcases hbetween with hbetween | hbetween <;> linarith
            · have hy_le_z : f y ≤ f z :=
                (List.pairwise_cons.mp hpair_tail).1 z hzys
              have hx_le_z : f x ≤ f z := hx_le_tail z (by simp [hzys])
              rcases hbetween with hbetween | hbetween <;> linarith
      · rcases hz with hzEq | hzTail
        · have hend := endpoints_mem_of_mem_consecutiveEdges (l := y :: ys) htail
          subst z
          have hxa : f x ≤ f a := hx_le_tail a hend.1
          have hxb : f x ≤ f b := hx_le_tail b hend.2
          intro hbetween
          rcases hbetween with hbetween | hbetween <;> linarith
        · exact not_key_between_of_mem_consecutiveEdges_pairwise hpair_tail htail hzTail

lemma midpoint_lineMap_average (P Q : ℝ × ℝ) (ta tb : ℝ) :
    midpoint ℝ (AffineMap.lineMap P Q ta) (AffineMap.lineMap P Q tb) =
      AffineMap.lineMap P Q ((ta + tb) / 2) := by
  ext <;> simp [AffineMap.lineMap_apply, midpoint] <;> ring

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

lemma mem_sideChain_of_onSide_engine {p q w : D.vtx}
    (hw : OnSide D p q w) :
    w ∈ p :: sideInteriorChain D p q ++ [q] := by
  by_cases hwp : w = p
  · simp [hwp]
  by_cases hwq : w = q
  · simp [hwq]
  have hwint : w ∈ sideInteriorChain D p q := by
    rw [mem_sideInteriorChain_iff]
    exact ⟨hw, hwp, hwq⟩
  simp [hwint]

lemma sideParam_injective_onSide_engine {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hparam : sideParam D p q a = sideParam D p q b) :
    a = b := by
  rcases sideParam_of_onSide D hpq ha with ⟨ta, _hta, ha_coord, hpa⟩
  rcases sideParam_of_onSide D hpq hb with ⟨tb, _htb, hb_coord, hpb⟩
  apply D.coord_inj
  calc
    D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := ha_coord
    _ = AffineMap.lineMap (D.coord p) (D.coord q) tb := by
      congr 1
      exact hpa ▸ hparam ▸ hpb
    _ = D.coord b := hb_coord.symm

lemma lineMap_lineMap_param_engine (P Q : ℝ × ℝ) (ta tb r : ℝ) :
    AffineMap.lineMap
        (AffineMap.lineMap P Q ta) (AffineMap.lineMap P Q tb) r =
      AffineMap.lineMap P Q ((1 - r) * ta + r * tb) := by
  ext <;> simp [AffineMap.lineMap_apply] <;> ring

lemma sbtw_of_sideParam_between_engine {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (haz : sideParam D p q a < sideParam D p q z)
    (hzb : sideParam D p q z < sideParam D p q b) :
    Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  rcases sideParam_of_onSide D hpq ha with ⟨ta', _hta, ha_coord, hpa⟩
  rcases sideParam_of_onSide D hpq hz with ⟨tz', _htz, hz_coord, hpz⟩
  rcases sideParam_of_onSide D hpq hb with ⟨tb', _htb, hb_coord, hpb⟩
  have ha_coord_ta :
      D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := by
    simpa [ta, hpa] using ha_coord
  have hz_coord_tz :
      D.coord z = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
    simpa [tz, hpz] using hz_coord
  have hb_coord_tb :
      D.coord b = AffineMap.lineMap (D.coord p) (D.coord q) tb := by
    simpa [tb, hpb] using hb_coord
  have hden : tb - ta ≠ 0 := by
    dsimp [ta, tb]
    linarith
  have hden_pos : 0 < tb - ta := by
    dsimp [ta, tb]
    linarith
  have hnumer_pos : 0 < tz - ta := by
    dsimp [ta, tz]
    linarith
  let r : ℝ := (tz - ta) / (tb - ta)
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [r, ta, tz, tb]
      exact div_pos hnumer_pos hden_pos
    · dsimp [r, ta, tz, tb]
      rw [div_lt_one (sub_pos.mpr (by simpa [ta, tz, tb] using haz.trans hzb))]
      linarith
  rw [sbtw_iff_mem_image_Ioo_and_ne]
  constructor
  · refine ⟨r, hr, ?_⟩
    calc
      AffineMap.lineMap (D.coord a) (D.coord b) r
          = AffineMap.lineMap
              (AffineMap.lineMap (D.coord p) (D.coord q) ta)
              (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
              rw [ha_coord_ta, hb_coord_tb]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
              rw [lineMap_lineMap_param_engine]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord z := by
              exact hz_coord_tz.symm
  · intro hab
    have habv : a = b := D.coord_inj hab
    subst b
    linarith

lemma sideParam_between_of_sbtw_engine {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (hs : Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b) ∨
      (sideParam D p q b < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q a) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  rcases sideParam_of_onSide D hpq ha with ⟨ta', _hta, ha_coord, hpa⟩
  rcases sideParam_of_onSide D hpq hz with ⟨tz', _htz, hz_coord, hpz⟩
  rcases sideParam_of_onSide D hpq hb with ⟨tb', _htb, hb_coord, hpb⟩
  have ha_coord_ta :
      D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := by
    simpa [ta, hpa] using ha_coord
  have hz_coord_tz :
      D.coord z = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
    simpa [tz, hpz] using hz_coord
  have hb_coord_tb :
      D.coord b = AffineMap.lineMap (D.coord p) (D.coord q) tb := by
    simpa [tb, hpb] using hb_coord
  rcases hs.mem_image_Ioo with ⟨r, hr, hzr⟩
  have hz_param : tz = (1 - r) * ta + r * tb := by
    dsimp [tz]
    apply sideParam_eq_of_lineMap D hpq
    calc
      D.coord z = AffineMap.lineMap (D.coord a) (D.coord b) r := hzr.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
            rw [ha_coord_ta, hb_coord_tb]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
            rw [lineMap_lineMap_param_engine]
  have hne_param : ta ≠ tb := by
    intro htab
    have hcoord : D.coord a = D.coord b := by
      calc
        D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := ha_coord_ta
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tb := by rw [htab]
        _ = D.coord b := hb_coord_tb.symm
    exact hs.left_ne_right hcoord
  rcases lt_or_gt_of_ne hne_param with hlt | hgt
  · left
    change ta < tz ∧ tz < tb
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hlt]
  · right
    change tb < tz ∧ tz < ta
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hgt]

lemma mem_consecutiveEdges_of_pairwise_no_between_engine
    {α : Type*} {f : α → ℝ} {P : α → Prop} :
    ∀ {l : List α} {a b : α},
      l.Nodup →
      (∀ x, x ∈ l → P x) →
      (∀ x y, P x → P y → f x = f y → x = y) →
      l.Pairwise (fun x y => f x ≤ f y) →
      a ∈ l → b ∈ l → f a < f b →
      (∀ z, z ∈ l → ¬ (f a < f z ∧ f z < f b)) →
      s(a, b) ∈ consecutiveEdges l
  | [], a, b, _hnd, _hall, _hinj, _hpair, ha, _hb, _hlt, _hno => by
      simp at ha
  | x :: [], a, b, _hnd, _hall, _hinj, _hpair, ha, hb, hlt, _hno => by
      simp at ha hb
      subst a
      subst b
      linarith
  | x :: y :: ys, a, b, hnd, hall, hinj, hpair, ha, hb, hlt, hno => by
      rw [consecutiveEdges, List.mem_cons]
      rw [List.mem_cons] at ha hb
      have hpair' := List.pairwise_cons.mp hpair
      have hx_le_tail : ∀ t ∈ y :: ys, f x ≤ f t := hpair'.1
      have htail_pair : (y :: ys).Pairwise (fun x y => f x ≤ f y) := hpair'.2
      have htail_nd : (y :: ys).Nodup := List.Nodup.of_cons hnd
      have htail_all : ∀ z, z ∈ y :: ys → P z := by
        intro z hz
        exact hall z (by simp [hz])
      rcases ha with rfl | ha_tail
      · rcases hb with rfl | hb_tail
        · linarith
        · rw [List.mem_cons] at hb_tail
          rcases hb_tail with rfl | hb_ys
          · exact Or.inl rfl
          · have hxy_le : f a ≤ f y := hx_le_tail y (by simp)
            have hxy_ne : a ≠ y := by
              intro hxy
              exact (List.Nodup.notMem hnd) (by simp [hxy])
            have hxy_lt : f a < f y := by
              refine lt_of_le_of_ne hxy_le ?_
              intro heq
              exact hxy_ne (hinj a y (hall a (by simp)) (hall y (by simp)) heq)
            have hy_le_b : f y ≤ f b :=
              (List.pairwise_cons.mp htail_pair).1 b hb_ys
            have hy_ne_b : y ≠ b := by
              intro hyb
              subst b
              exact (List.Nodup.notMem htail_nd) hb_ys
            have hy_lt_b : f y < f b := by
              refine lt_of_le_of_ne hy_le_b ?_
              intro heq
              exact hy_ne_b (hinj y b (hall y (by simp))
                (hall b (by simp [hb_ys])) heq)
            exact False.elim (hno y (by simp) ⟨hxy_lt, hy_lt_b⟩)
      · rcases hb with rfl | hb_tail
        · have hx_le_a : f b ≤ f a := hx_le_tail a ha_tail
          exact False.elim (by linarith)
        · exact Or.inr
            (mem_consecutiveEdges_of_pairwise_no_between_engine
              (l := y :: ys) (f := f) (P := P)
              htail_nd htail_all hinj htail_pair ha_tail hb_tail hlt
              (fun z hz => hno z (by simp [hz])))

lemma mem_sideAtomicEdges_of_onSide_no_sideParam_between_engine
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hlt : sideParam D p q a < sideParam D p q b)
    (hno : ∀ z : D.vtx, OnSide D p q z →
      ¬ (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  let chain := p :: sideInteriorChain D p q ++ [q]
  have ha_mem : a ∈ chain := mem_sideChain_of_onSide_engine (D := D) ha
  have hb_mem : b ∈ chain := mem_sideChain_of_onSide_engine (D := D) hb
  have hall : ∀ x, x ∈ chain → OnSide D p q x := by
    intro x hx
    exact onSide_of_mem_sideChain D hx
  unfold sideAtomicEdges
  exact mem_consecutiveEdges_of_pairwise_no_between_engine
    (l := chain) (f := sideParam D p q) (P := fun x => OnSide D p q x)
    (sideChain_nodup D hpq) hall
    (fun x y hx hy hxy => sideParam_injective_onSide_engine D hpq hx hy hxy)
    (sideChain_pairwise D hpq) ha_mem hb_mem hlt
    (fun z hz => hno z (hall z hz))

lemma mem_sideAtomicEdges_of_onSide_no_sbtw_engine
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hab : a ≠ b)
    (hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  have hparam_ne : sideParam D p q a ≠ sideParam D p q b := by
    intro hparam
    exact hab (sideParam_injective_onSide_engine D hpq ha hb hparam)
  rcases lt_or_gt_of_ne hparam_ne with hlt | hgt
  · exact mem_sideAtomicEdges_of_onSide_no_sideParam_between_engine (D := D) hpq ha hb hlt
      (fun z hz hbetween =>
        hno z (sbtw_of_sideParam_between_engine (D := D) hpq ha hb hz hbetween.1 hbetween.2))
  · have hmem : s(b, a) ∈ sideAtomicEdges D p q :=
      mem_sideAtomicEdges_of_onSide_no_sideParam_between_engine (D := D) hpq hb ha hgt
        (fun z hz hbetween =>
          hno z ((sbtw_of_sideParam_between_engine (D := D) hpq hb ha hz
            hbetween.1 hbetween.2).symm))
    simpa [Sym2.eq_swap] using hmem

lemma not_sbtw_of_mem_sideAtomicEdges_engine {p q a b z : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  intro hs
  have hmem :
      s(a, b) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
    simpa [sideAtomicEdges] using h
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D h
  have hzseg :
      D.coord z ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide D hon.1 hon.2 hs.wbtw.mem_segment
  have hzon : OnSide D p q z := (mem_segment_iff_wbtw (R := ℝ)).mp hzseg
  have hzmem : z ∈ p :: sideInteriorChain D p q ++ [q] :=
    mem_sideChain_of_onSide_engine (D := D) hzon
  rcases sideParam_between_of_sbtw_engine (D := D) hpq hon.1 hon.2 hzon hs with hbetween | hbetween
  · exact not_key_between_of_mem_consecutiveEdges_pairwise
      (f := sideParam D p q) (sideChain_pairwise D hpq) hmem hzmem (Or.inl hbetween)
  · have hswap : s(b, a) ∈ sideAtomicEdges D p q := by
      simpa [Sym2.eq_swap] using h
    have hmemswap :
        s(b, a) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
      simpa [sideAtomicEdges] using hswap
    exact not_key_between_of_mem_consecutiveEdges_pairwise
      (f := sideParam D p q) (sideChain_pairwise D hpq) hmemswap hzmem (Or.inl hbetween)

lemma midpoint_ne_vertex_of_mem_sideAtomicEdges {p q a b : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q)
    (z : D.vtx) :
    D.coord z ≠ midpoint ℝ (D.coord a) (D.coord b) := by
  intro hzmid
  have hmem :
      s(a, b) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
    simpa [sideAtomicEdges] using h
  have hpair := sideChain_pairwise D hpq
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D h
  rcases sideParam_of_onSide D hpq hon.1 with ⟨ta, hta, hA, hpa⟩
  rcases sideParam_of_onSide D hpq hon.2 with ⟨tb, htb, hB, hpb⟩
  have hne_ab : a ≠ b := ne_of_mk_mem_sideAtomicEdges D hpq h
  have hcoord_ab : D.coord a ≠ D.coord b := by
    intro hcoord
    exact hne_ab (D.coord_inj hcoord)
  have hta_ne_tb : ta ≠ tb := by
    intro htab
    apply hcoord_ab
    rw [hA, hB, htab]
  have hz_line :
      D.coord z = AffineMap.lineMap (D.coord p) (D.coord q) ((ta + tb) / 2) := by
    rw [hzmid, hA, hB, midpoint_lineMap_average]
  have hpz : sideParam D p q z = (ta + tb) / 2 :=
    sideParam_eq_of_lineMap D hpq hz_line
  have hmid_open :
      midpoint ℝ (D.coord a) (D.coord b) ∈
        openSegment ℝ (D.coord p) (D.coord q) :=
    midpoint_mem_openSegment_of_wbtw_of_ne hon.1 hon.2 hcoord_ab
  have hzopen : D.coord z ∈ openSegment ℝ (D.coord p) (D.coord q) := by
    simpa [hzmid] using hmid_open
  have hzon : OnSide D p q z := by
    exact (mem_segment_iff_wbtw (R := ℝ)).mp
      (openSegment_subset_segment ℝ (D.coord p) (D.coord q) hzopen)
  have hzp : z ≠ p := by
    intro hzp
    have hpopen : D.coord p ∈ openSegment ℝ (D.coord p) (D.coord q) := by
      simpa [hzp] using hzopen
    have hpqcoord : D.coord p = D.coord q := left_mem_openSegment_iff.mp hpopen
    exact hpq (D.coord_inj hpqcoord)
  have hzq : z ≠ q := by
    intro hzq
    have hqopen : D.coord q ∈ openSegment ℝ (D.coord p) (D.coord q) := by
      simpa [hzq] using hzopen
    have hpqcoord : D.coord p = D.coord q := right_mem_openSegment_iff.mp hqopen
    exact hpq (D.coord_inj hpqcoord)
  have hzchain : z ∈ sideInteriorChain D p q := by
    rw [mem_sideInteriorChain_iff]
    exact ⟨hzon, hzp, hzq⟩
  have hzmem : z ∈ p :: sideInteriorChain D p q ++ [q] := by
    simp [hzchain]
  have hno :=
    not_key_between_of_mem_consecutiveEdges_pairwise
      (f := sideParam D p q) hpair hmem hzmem
  apply hno
  rcases lt_or_gt_of_ne hta_ne_tb with hlt | hgt
  · left
    rw [hpa, hpb, hpz]
    constructor <;> nlinarith
  · right
    rw [hpa, hpb, hpz]
    constructor <;> nlinarith

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

lemma ne_of_mk_mem_triAtomicEdges {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) : a ≠ b := by
  rw [mem_triAtomicEdges_iff] at h
  rcases h with h | h | h
  · exact ne_of_mk_mem_sideAtomicEdges D (tri_v₁_ne_v₂ D i) h
  · exact ne_of_mk_mem_sideAtomicEdges D (tri_v₂_ne_v₃ D i) h
  · exact ne_of_mk_mem_sideAtomicEdges D (tri_v₃_ne_v₁ D i) h

lemma not_sbtw_of_mem_triAtomicEdges_engine {i : Fin D.n} {a b z : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  rw [mem_triAtomicEdges_iff] at h
  rcases h with h | h | h
  · exact not_sbtw_of_mem_sideAtomicEdges_engine D (tri_v₁_ne_v₂ D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges_engine D (tri_v₂_ne_v₃ D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges_engine D (tri_v₃_ne_v₁ D i) h





theorem atomicEdge_midpoint_ne_vertex {a b : D.vtx} (i : Fin D.n)
    (hmem : s(a, b) ∈ triAtomicEdges D i) (z : D.vtx) :
    D.coord z ≠ midpoint ℝ (D.coord a) (D.coord b) := by
  rw [mem_triAtomicEdges_iff] at hmem
  rcases hmem with h | h | h
  · exact midpoint_ne_vertex_of_mem_sideAtomicEdges D (tri_v₁_ne_v₂ D i) h z
  · exact midpoint_ne_vertex_of_mem_sideAtomicEdges D (tri_v₂_ne_v₃ D i) h z
  · exact midpoint_ne_vertex_of_mem_sideAtomicEdges D (tri_v₃_ne_v₁ D i) h z

lemma no_transversal_openSegments_of_disjoint_int
    {i k : Fin D.n} (hik : i ≠ k)
    {a b c u v w m : ℝ × ℝ}
    (hi : triHull D i = convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
    (hk : triHull D k = convexHull ℝ ({u, v, w} : Set (ℝ × ℝ)))
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (habuv : doubleArea a b (m + (v - u)) ≠ 0)
    (huvab : doubleArea u v (m + (b - a)) ≠ 0) :
    False := by
  obtain ⟨d, hdab, hduv⟩ :=
    exists_common_sameSide_of_transversal_directions a b c u v w m
      habc huvw hmab hmuv habuv huvab
  obtain ⟨x, hxi, hxk⟩ :=
    exists_common_interior_of_common_sameSide a b c u v w d m
      habc huvw hmab hmuv hdab hduv
  have hxi' : x ∈ interior (triHull D i) := by
    simpa [hi] using hxi
  have hxk' : x ∈ interior (triHull D k) := by
    simpa [hk] using hxk
  exact Set.disjoint_left.mp (D.disjoint_int i k hik) hxi' hxk'

lemma midpoint_mem_openSegment_of_mem_sideAtomicEdges {p q a b : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q) :
    midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord p) (D.coord q) := by
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D h
  have hab : D.coord a ≠ D.coord b := by
    exact fun hcoord => ne_of_mk_mem_sideAtomicEdges D hpq h (D.coord_inj hcoord)
  exact midpoint_mem_openSegment_of_wbtw_of_ne hon.1 hon.2 hab



lemma segment_subset_triHull_of_mem_sideAtomicEdges {i : Fin D.n} {p q a b : D.vtx}
    (hp : p ∈ ({(D.tri i).1, (D.tri i).2.1, (D.tri i).2.2} : Set D.vtx))
    (hq : q ∈ ({(D.tri i).1, (D.tri i).2.1, (D.tri i).2.2} : Set D.vtx))
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    segment ℝ (D.coord a) (D.coord b) ⊆ triHull D i := by
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D h
  have hABpq : segment ℝ (D.coord a) (D.coord b) ⊆
      segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide D hon.1 hon.2
  have hpcoord :
      D.coord p ∈
        ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
          D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) := by
    rcases hp with rfl | rfl | rfl <;> simp
  have hqcoord :
      D.coord q ∈
        ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
          D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) := by
    rcases hq with rfl | rfl | rfl <;> simp
  exact hABpq.trans (by
    unfold triHull
    exact segment_subset_convexHull hpcoord hqcoord)

lemma segment_subset_triHull_of_mem_triAtomicEdges {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    segment ℝ (D.coord a) (D.coord b) ⊆ triHull D i := by
  rw [mem_triAtomicEdges_iff] at h
  rcases h with h | h | h
  · exact segment_subset_triHull_of_mem_sideAtomicEdges D (by simp) (by simp) h
  · exact segment_subset_triHull_of_mem_sideAtomicEdges D (by simp) (by simp) h
  · exact segment_subset_triHull_of_mem_sideAtomicEdges D (by simp) (by simp) h

lemma segment_subset_unitSquare_of_mem_triAtomicEdges {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    segment ℝ (D.coord a) (D.coord b) ⊆ unitSquareSet :=
  (segment_subset_triHull_of_mem_triAtomicEdges D h).trans (triHull_subset_unitSquare D i)



lemma fst_eq_of_mem_segment_of_fst_eq {A B x : ℝ × ℝ} {c : ℝ}
    (hA : A.1 = c) (hB : B.1 = c) (hx : x ∈ segment ℝ A B) : x.1 = c := by
  rw [segment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  simp [AffineMap.lineMap_apply, hA, hB]
  ring

lemma snd_eq_of_mem_segment_of_snd_eq {A B x : ℝ × ℝ} {c : ℝ}
    (hA : A.2 = c) (hB : B.2 = c) (hx : x ∈ segment ℝ A B) : x.2 = c := by
  rw [segment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  simp [AffineMap.lineMap_apply, hA, hB]
  ring

lemma segment_subset_frontier_unitSquare_of_midpoint_mem_frontier
    {A B : ℝ × ℝ}
    (hseg : segment ℝ A B ⊆ unitSquareSet)
    (hm : midpoint ℝ A B ∈ frontier unitSquareSet) :
    segment ℝ A B ⊆ frontier unitSquareSet := by
  intro x hx
  have hA : A ∈ unitSquareSet := hseg (left_mem_segment ℝ A B)
  have hB : B ∈ unitSquareSet := hseg (right_mem_segment ℝ A B)
  have hxSq : x ∈ unitSquareSet := hseg hx
  have hA' : (0 ≤ A.1 ∧ 0 ≤ A.2) ∧ A.1 ≤ 1 ∧ A.2 ≤ 1 := by
    simpa [unitSquareSet, Set.mem_Icc, Prod.le_def] using hA
  have hB' : (0 ≤ B.1 ∧ 0 ≤ B.2) ∧ B.1 ≤ 1 ∧ B.2 ≤ 1 := by
    simpa [unitSquareSet, Set.mem_Icc, Prod.le_def] using hB
  have hxSq' : (0 ≤ x.1 ∧ 0 ≤ x.2) ∧ x.1 ≤ 1 ∧ x.2 ≤ 1 := by
    simpa [unitSquareSet, Set.mem_Icc, Prod.le_def] using hxSq
  have hm' :
      midpoint ℝ A B ∈
        frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
    simpa [unitSquareSet] using hm
  rw [frontier_unitSquare] at hm'
  rcases hm' with ⟨_, _, _, _, hmcase⟩
  have hfrontSet :
      x ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)} := by
    refine ⟨hxSq'.1.1, hxSq'.2.1, hxSq'.1.2, hxSq'.2.2, ?_⟩
    rcases hmcase with hm0 | hm1 | hm0 | hm1
    · have hmid : A.1 + B.1 = 0 := by
        have hmid' := hm0
        simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at hmid'
        linarith
      have hA0 : A.1 = 0 := by nlinarith [hA'.1.1, hB'.1.1, hmid]
      have hB0 : B.1 = 0 := by nlinarith [hA'.1.1, hB'.1.1, hmid]
      exact Or.inl (fst_eq_of_mem_segment_of_fst_eq hA0 hB0 hx)
    · have hmid : A.1 + B.1 = 2 := by
        have hmid' := hm1
        simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at hmid'
        linarith
      have hA1 : A.1 = 1 := by nlinarith [hA'.2.1, hB'.2.1, hmid]
      have hB1 : B.1 = 1 := by nlinarith [hA'.2.1, hB'.2.1, hmid]
      exact Or.inr <| Or.inl (fst_eq_of_mem_segment_of_fst_eq hA1 hB1 hx)
    · have hmid : A.2 + B.2 = 0 := by
        have hmid' := hm0
        simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at hmid'
        linarith
      have hA0 : A.2 = 0 := by nlinarith [hA'.1.2, hB'.1.2, hmid]
      have hB0 : B.2 = 0 := by nlinarith [hA'.1.2, hB'.1.2, hmid]
      exact Or.inr <| Or.inr <| Or.inl (snd_eq_of_mem_segment_of_snd_eq hA0 hB0 hx)
    · have hmid : A.2 + B.2 = 2 := by
        have hmid' := hm1
        simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at hmid'
        linarith
      have hA1 : A.2 = 1 := by nlinarith [hA'.2.2, hB'.2.2, hmid]
      have hB1 : B.2 = 1 := by nlinarith [hA'.2.2, hB'.2.2, hmid]
      exact Or.inr <| Or.inr <| Or.inr (snd_eq_of_mem_segment_of_snd_eq hA1 hB1 hx)
  simpa [frontier_unitSquare] using hfrontSet



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









lemma triSide_hull (i : Fin D.n) (j : Fin 3) :
    triHull D i =
      convexHull ℝ
        ({D.coord (triSideP D i j), D.coord (triSideQ D i j),
          D.coord (triSideR D i j)} : Set (ℝ × ℝ)) := by
  fin_cases j <;>
    unfold triSideP triSideQ triSideR triHull <;>
    simp <;>
    try (congr 1; ext x; simp; tauto)

lemma triSide_nondeg (i : Fin D.n) (j : Fin 3) :
    doubleArea (D.coord (triSideP D i j)) (D.coord (triSideQ D i j))
      (D.coord (triSideR D i j)) ≠ 0 := by
  fin_cases j
  · simpa [triSideP, triSideQ, triSideR] using D.nondeg i
  · simpa [triSideP, triSideQ, triSideR] using doubleArea_ne_zero_cycle₁ (D.nondeg i)
  · simpa [triSideP, triSideQ, triSideR] using doubleArea_ne_zero_cycle₂ (D.nondeg i)

lemma triSideSegment_closed (ij : Fin D.n × Fin 3) :
    IsClosed (triSideSegment D ij) := by
  have hfin :
      ({D.coord (triSideP D ij.1 ij.2),
        D.coord (triSideQ D ij.1 ij.2)} : Set (ℝ × ℝ)).Finite := by
    simp
  simpa [triSideSegment, convexHull_pair] using
    hfin.isClosed_convexHull (𝕜 := ℝ)

lemma triSideSegment_nonempty (ij : Fin D.n × Fin 3) :
    (triSideSegment D ij).Nonempty := by
  exact ⟨D.coord (triSideP D ij.1 ij.2),
    by
      unfold triSideSegment
      exact left_mem_segment ℝ _ _⟩

lemma exists_triSide_of_mem_frontier_triHull {i : Fin D.n} {x : ℝ × ℝ}
    (hx : x ∈ frontier (triHull D i)) :
    ∃ j : Fin 3, x ∈ triSideSegment D (i, j) := by
  have hfront :=
    frontier_convexHull_triangle_of_doubleArea_ne_zero
      (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2)
      (D.nondeg i)
  rw [triHull, hfront] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · exact ⟨0, by simpa [triSideSegment, triSideP, triSideQ] using hx⟩
    · exact ⟨1, by simpa [triSideSegment, triSideP, triSideQ] using hx⟩
  · exact ⟨2, by simpa [triSideSegment, triSideP, triSideQ] using hx⟩

lemma triSideSegment_subset_frontier_triHull (i : Fin D.n) (j : Fin 3) :
    triSideSegment D (i, j) ⊆ frontier (triHull D i) := by
  intro x hx
  rw [triSide_hull D i j,
    frontier_convexHull_triangle_of_doubleArea_ne_zero
      (D.coord (triSideP D i j)) (D.coord (triSideQ D i j))
      (D.coord (triSideR D i j)) (triSide_nondeg D i j)]
  exact Or.inl (Or.inl (by simpa [triSideSegment] using hx))

lemma midpoint_mem_frontier_triHull_of_mem_triAtomicEdges
    {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    midpoint ℝ (D.coord a) (D.coord b) ∈ frontier (triHull D i) := by
  rw [mem_triAtomicEdges_iff] at h
  rcases h with h | h | h
  · exact triSideSegment_subset_frontier_triHull D i 0
      (openSegment_subset_segment ℝ _ _
        (midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₁_ne_v₂ D i) h))
  · exact triSideSegment_subset_frontier_triHull D i 1
      (openSegment_subset_segment ℝ _ _
        (midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₂_ne_v₃ D i) h))
  · exact triSideSegment_subset_frontier_triHull D i 2
      (openSegment_subset_segment ℝ _ _
        (midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₃_ne_v₁ D i) h))

lemma midpoint_mem_openSegment_of_mem_triSideSegment_of_atomic
    {i₀ k : Fin D.n} {a b : D.vtx} {j : Fin 3}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hm : midpoint ℝ (D.coord a) (D.coord b) ∈ triSideSegment D (k, j)) :
    midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord (triSideP D k j)) (D.coord (triSideQ D k j)) := by
  exact mem_openSegment_of_ne_left_right
    (atomicEdge_midpoint_ne_vertex D i₀ h₀ (triSideP D k j))
    (atomicEdge_midpoint_ne_vertex D i₀ h₀ (triSideQ D k j))
    (by simpa [triSideSegment] using hm)

lemma exists_openSegment_point_dist_lt
    {m r : ℝ × ℝ} (hmr : m ≠ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ × ℝ, x ∈ openSegment ℝ m r ∧ dist x m < ε := by
  let v : ℝ × ℝ := r - m
  have hv_ne : v ≠ 0 := by
    intro hv
    apply hmr
    ext
    · have h := congrArg Prod.fst hv
      simp [v] at h
      linarith
    · have h := congrArg Prod.snd hv
      simp [v] at h
      linarith
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  let t : ℝ := min (1 / 2) (ε / (2 * ‖v‖))
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (by positivity)
  have htlt : t < 1 := by
    dsimp [t]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let x : ℝ × ℝ := AffineMap.lineMap m r t
  refine ⟨x, ?_, ?_⟩
  · rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨htpos, htlt⟩, rfl⟩
  · have hdist : dist x m = t * ‖v‖ := by
      rw [dist_eq_norm]
      have hxsub : x - m = t • v := by
        ext <;> simp [x, v, AffineMap.lineMap_apply] <;> ring
      rw [hxsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have ht_le : t ≤ ε / (2 * ‖v‖) := by
      dsimp [t]
      exact min_le_right _ _
    have hmul_le : t * ‖v‖ ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_right ht_le (le_of_lt hv_norm_pos)
      have hcalc : ε / (2 * ‖v‖) * ‖v‖ = ε / 2 := by
        field_simp [ne_of_gt hv_norm_pos]
      linarith
    rw [hdist]
    linarith

lemma doubleArea_eq_zero_of_mem_segment_parallel_left
    {A B U V m x : ℝ × ℝ}
    (hmAB : doubleArea A B m = 0)
    (hmUV : m ∈ segment ℝ U V) (hxUV : x ∈ segment ℝ U V)
    (hpar : doubleArea A B (m + (V - U)) = 0) :
    doubleArea A B x = 0 := by
  rw [segment_eq_image] at hmUV hxUV
  rcases hmUV with ⟨tm, _htm, hm⟩
  rcases hxUV with ⟨tx, _htx, hx⟩
  rw [← hm] at hmAB hpar
  rw [← hx]
  unfold doubleArea at *
  simp [AffineMap.lineMap_apply] at *
  linear_combination (1 - (tx - tm)) * hmAB + (tx - tm) * hpar

lemma doubleArea_eq_zero_of_mem_segment_parallel_right
    {A B U V m x : ℝ × ℝ}
    (hmAB : doubleArea A B m = 0)
    (hmUV : m ∈ segment ℝ U V) (hxUV : x ∈ segment ℝ U V)
    (hpar : doubleArea U V (m + (B - A)) = 0) :
    doubleArea A B x = 0 := by
  rw [segment_eq_image] at hmUV hxUV
  rcases hmUV with ⟨tm, _htm, hm⟩
  rcases hxUV with ⟨tx, _htx, hx⟩
  rw [← hm] at hmAB hpar
  rw [← hx]
  unfold doubleArea at *
  simp [AffineMap.lineMap_apply] at *
  linear_combination hmAB - (tx - tm) * hpar

lemma doubleArea_add_direction_of_wbtw_eq_zero
    {U V P Q A B m : ℝ × ℝ}
    (ha : Wbtw ℝ P A Q) (hb : Wbtw ℝ P B Q)
    (hm : doubleArea U V m = 0)
    (hdir : doubleArea U V (m + (Q - P)) = 0) :
    doubleArea U V (m + (B - A)) = 0 := by
  obtain ⟨ta, _hta, hA⟩ := ha
  obtain ⟨tb, _htb, hB⟩ := hb
  rw [← hA, ← hB]
  unfold doubleArea at *
  simp [AffineMap.lineMap_apply] at *
  linear_combination (1 - (tb - ta)) * hm + (tb - ta) * hdir

lemma doubleArea_atomic_line_eq_zero_of_mem_sideAtomicEdges
    {p q a b : D.vtx} {x : ℝ × ℝ}
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hx : x ∈ segment ℝ (D.coord p) (D.coord q)) :
    doubleArea (D.coord a) (D.coord b) x = 0 := by
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D hside
  obtain ⟨_ta, _tb, _ha, _hb, harea⟩ :=
    doubleArea_of_two_wbtw_on_side hon.1 hon.2 (r := x)
  rw [harea, doubleArea_eq_zero_of_mem_segment hx, mul_zero]

lemma not_mem_other_triangle_sides_of_mem_openSegment
    {P Q R m : ℝ × ℝ}
    (hnd : doubleArea P Q R ≠ 0)
    (hm : m ∈ openSegment ℝ P Q) :
    m ∉ segment ℝ Q R ∧ m ∉ segment ℝ R P := by
  have hPQ : P ≠ Q := by
    intro h
    exact hnd (by simp [h, doubleArea])
  have hmSeg : m ∈ segment ℝ P Q := openSegment_subset_segment ℝ P Q hm
  constructor
  · intro hmQR
    have hli :
        LinearIndependent ℝ ![P - Q, R - Q] :=
      linearIndependent_pair_of_doubleArea_ne_zero Q P R
        (doubleArea_ne_zero_perm₂₁₃ hnd)
    have hinter :
        segment ℝ Q P ∩ segment ℝ Q R = {Q} :=
      segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hli
    have hmInter : m ∈ segment ℝ Q P ∩ segment ℝ Q R := by
      exact ⟨by simpa [segment_symm] using hmSeg, hmQR⟩
    have hmQ : m = Q := by
      simpa [hinter] using hmInter
    have hQopen : Q ∈ openSegment ℝ P Q := by
      simpa [hmQ] using hm
    exact hPQ (right_mem_openSegment_iff.mp hQopen)
  · intro hmRP
    have hli :
        LinearIndependent ℝ ![Q - P, R - P] :=
      linearIndependent_pair_of_doubleArea_ne_zero P Q R hnd
    have hinter :
        segment ℝ P Q ∩ segment ℝ P R = {P} :=
      segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hli
    have hmInter : m ∈ segment ℝ P Q ∩ segment ℝ P R := by
      exact ⟨hmSeg, by simpa [segment_symm] using hmRP⟩
    have hmP : m = P := by
      simpa [hinter] using hmInter
    have hPopen : P ∈ openSegment ℝ P Q := by
      simpa [hmP] using hm
    exact hPQ (left_mem_openSegment_iff.mp hPopen)

lemma doubleArea_eq_zero_of_mem_same_triSide_containing_atomic_midpoint
    {i : Fin D.n} {a b : D.vtx} {j : Fin 3} {x : ℝ × ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i)
    (hm : midpoint ℝ (D.coord a) (D.coord b) ∈ triSideSegment D (i, j))
    (hx : x ∈ triSideSegment D (i, j)) :
    doubleArea (D.coord a) (D.coord b) x = 0 := by
  rw [mem_triAtomicEdges_iff] at h₀
  rcases h₀ with h₀ | h₀ | h₀
  · have hmSide :
        midpoint ℝ (D.coord a) (D.coord b) ∈
          openSegment ℝ (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) :=
      midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₁_ne_v₂ D i) h₀
    fin_cases j
    · exact doubleArea_atomic_line_eq_zero_of_mem_sideAtomicEdges D h₀
        (by simpa [triSideSegment, triSideP, triSideQ] using hx)
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (D.nondeg i) hmSide).1
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (D.nondeg i) hmSide).2
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
  · have hmSide :
        midpoint ℝ (D.coord a) (D.coord b) ∈
          openSegment ℝ (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2) :=
      midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₂_ne_v₃ D i) h₀
    fin_cases j
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (doubleArea_ne_zero_cycle₁ (D.nondeg i)) hmSide).2
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
    · exact doubleArea_atomic_line_eq_zero_of_mem_sideAtomicEdges D h₀
        (by simpa [triSideSegment, triSideP, triSideQ] using hx)
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (doubleArea_ne_zero_cycle₁ (D.nondeg i)) hmSide).1
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
  · have hmSide :
        midpoint ℝ (D.coord a) (D.coord b) ∈
          openSegment ℝ (D.coord (D.tri i).2.2) (D.coord (D.tri i).1) :=
      midpoint_mem_openSegment_of_mem_sideAtomicEdges D (tri_v₃_ne_v₁ D i) h₀
    fin_cases j
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (doubleArea_ne_zero_cycle₂ (D.nondeg i)) hmSide).1
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
    · have hnot :=
        (not_mem_other_triangle_sides_of_mem_openSegment
          (doubleArea_ne_zero_cycle₂ (D.nondeg i)) hmSide).2
      exact False.elim (hnot (by simpa [triSideSegment, triSideP, triSideQ] using hm))
    · exact doubleArea_atomic_line_eq_zero_of_mem_sideAtomicEdges D h₀
        (by simpa [triSideSegment, triSideP, triSideQ] using hx)

lemma doubleArea_eq_zero_of_mem_triSideSegment_containing_atomic_midpoint
    {i₀ k : Fin D.n} {a b : D.vtx} {j : Fin 3} {x : ℝ × ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hm : midpoint ℝ (D.coord a) (D.coord b) ∈ triSideSegment D (k, j))
    (hx : x ∈ triSideSegment D (k, j)) :
    doubleArea (D.coord a) (D.coord b) x = 0 := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  by_cases hki : k = i₀
  · subst k
    exact doubleArea_eq_zero_of_mem_same_triSide_containing_atomic_midpoint D h₀
      (by simpa [m] using hm) hx
  · rcases exists_incidentSideWitness D h₀ with ⟨W₀, _⟩
    let U := D.coord (triSideP D k j)
    let V := D.coord (triSideQ D k j)
    let W := D.coord (triSideR D k j)
    have hpq : W₀.p ≠ W₀.q := by
      intro hpq
      exact W₀.hnd (by simp [hpq, doubleArea])
    have hmPQ :
        m ∈ openSegment ℝ (D.coord W₀.p) (D.coord W₀.q) := by
      simpa [m] using
        midpoint_mem_openSegment_of_mem_sideAtomicEdges D hpq W₀.hmem
    have hmUVopen :
        m ∈ openSegment ℝ U V := by
      simpa [m, U, V] using
        midpoint_mem_openSegment_of_mem_triSideSegment_of_atomic D h₀ hm
    have hmUV : m ∈ segment ℝ U V :=
      openSegment_subset_segment ℝ U V hmUVopen
    have hxUV : x ∈ segment ℝ U V := by
      simpa [U, V, triSideSegment] using hx
    have hmAB : doubleArea (D.coord a) (D.coord b) m = 0 := by
      exact doubleArea_eq_zero_of_mem_segment
        (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
    by_cases htrans₁ :
        doubleArea (D.coord W₀.p) (D.coord W₀.q) (m + (V - U)) ≠ 0
    · by_cases htrans₂ : doubleArea U V (m + (D.coord W₀.q - D.coord W₀.p)) ≠ 0
      · exact False.elim
          (no_transversal_openSegments_of_disjoint_int D (Ne.symm hki) W₀.hHull
            (by simpa [U, V, W] using triSide_hull D k j)
            W₀.hnd (by simpa [U, V, W] using triSide_nondeg D k j)
            hmPQ (by simpa [U, V] using hmUVopen)
            (by simpa [U, V] using htrans₁)
            (by simpa [U, V] using htrans₂))
      · have hzero₂ : doubleArea U V (m + (D.coord W₀.q - D.coord W₀.p)) = 0 :=
          not_not.mp htrans₂
        have hmUVarea : doubleArea U V m = 0 :=
          doubleArea_eq_zero_of_mem_segment hmUV
        have hon := endpoints_onSide_of_mem_sideAtomicEdges D W₀.hmem
        have hpar :
            doubleArea U V (m + (D.coord b - D.coord a)) = 0 :=
          doubleArea_add_direction_of_wbtw_eq_zero hon.1 hon.2 hmUVarea hzero₂
        exact doubleArea_eq_zero_of_mem_segment_parallel_right hmAB hmUV hxUV hpar
    · have hzero₁ :
          doubleArea (D.coord W₀.p) (D.coord W₀.q) (m + (V - U)) = 0 :=
        not_not.mp htrans₁
      have hon := endpoints_onSide_of_mem_sideAtomicEdges D W₀.hmem
      obtain ⟨_ta, _tb, _ha, _hb, harea⟩ :=
        doubleArea_of_two_wbtw_on_side hon.1 hon.2 (r := m + (V - U))
      have hpar : doubleArea (D.coord a) (D.coord b) (m + (V - U)) = 0 := by
        rw [harea, hzero₁, mul_zero]
      exact doubleArea_eq_zero_of_mem_segment_parallel_left hmAB hmUV hxUV hpar

lemma exists_lineMap_of_doubleArea_eq_zero {U V X : ℝ × ℝ}
    (hUV : U ≠ V) (harea : doubleArea U V X = 0) :
    ∃ t : ℝ, AffineMap.lineMap U V t = X := by
  rw [doubleArea_eq_zero_iff_collinear] at harea
  by_cases hx : V.1 ≠ U.1
  · let t : ℝ := (X.1 - U.1) / (V.1 - U.1)
    refine ⟨t, ?_⟩
    ext
    · simp [t, AffineMap.lineMap_apply]
      field_simp [hx]
      linarith
    · simp [t, AffineMap.lineMap_apply]
      field_simp [hx]
      have harea' :
          (V.1 - U.1) * (X.2 - U.2) -
            (X.1 - U.1) * (V.2 - U.2) = 0 := by
        linarith
      ring_nf at harea' ⊢
      linarith
  · have hy : V.2 - U.2 ≠ 0 := by
      intro hy
      apply hUV
      ext
      · exact (not_not.mp hx).symm
      · linarith
    let t : ℝ := (X.2 - U.2) / (V.2 - U.2)
    refine ⟨t, ?_⟩
    ext
    · simp [t, AffineMap.lineMap_apply]
      field_simp [hy]
      have harea' :
          (V.1 - U.1) * (X.2 - U.2) -
            (X.1 - U.1) * (V.2 - U.2) = 0 := by
        linarith
      ring_nf at harea' ⊢
      nlinarith
    · simp [t, AffineMap.lineMap_apply]
      field_simp [hy]
      linarith



lemma endpoints_onSide_of_midpoint_openSegment_of_collinear_no_sbtw
    {i₀ : Fin D.n} {a b u v : D.vtx}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (huv : u ≠ v)
    (hmuv : midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord u) (D.coord v))
    (huLine : doubleArea (D.coord a) (D.coord b) (D.coord u) = 0)
    (hvLine : doubleArea (D.coord a) (D.coord b) (D.coord v) = 0) :
    OnSide D u v a ∧ OnSide D u v b := by
  let A := D.coord a
  let B := D.coord b
  let U := D.coord u
  let V := D.coord v
  have hab : a ≠ b := ne_of_mk_mem_triAtomicEdges D h₀
  have hAB : A ≠ B := fun h => hab (D.coord_inj h)
  have hUV : U ≠ V := fun h => huv (D.coord_inj h)
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ A (D.coord z) B :=
    fun z => not_sbtw_of_mem_triAtomicEdges_engine D h₀
  rcases exists_lineMap_of_doubleArea_eq_zero hAB (by simpa [A, B, U] using huLine) with
    ⟨tu, hU⟩
  rcases exists_lineMap_of_doubleArea_eq_zero hAB (by simpa [A, B, V] using hvLine) with
    ⟨tv, hV⟩
  rw [openSegment_eq_image_lineMap] at hmuv
  rcases hmuv with ⟨r, hr, hm⟩
  have hhalf_param : (1 - r) * tu + r * tv = (1 : ℝ) / 2 := by
    apply AffineMap.lineMap_injective ℝ hAB
    calc
      AffineMap.lineMap A B ((1 - r) * tu + r * tv)
          = AffineMap.lineMap
              (AffineMap.lineMap A B tu) (AffineMap.lineMap A B tv) r := by
              rw [lineMap_lineMap_param_engine]
      _ = AffineMap.lineMap U V r := by rw [hU, hV]
      _ = midpoint ℝ A B := by simpa [A, B, U, V] using hm
      _ = AffineMap.lineMap A B ((1 : ℝ) / 2) := by
            ext <;> simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv] <;> ring
  have htu_ne_tv : tu ≠ tv := by
    intro h
    apply hUV
    calc
      U = AffineMap.lineMap A B tu := by simpa [U] using hU.symm
      _ = AffineMap.lineMap A B tv := by rw [h]
      _ = V := by simpa [V] using hV
  have hU_not_Ioo : ¬ tu ∈ Set.Ioo (0 : ℝ) 1 := by
    intro htu
    have hUbetween : Sbtw ℝ A U B := by
      rw [sbtw_iff_mem_image_Ioo_and_ne]
      exact ⟨⟨tu, htu, hU⟩, hAB⟩
    exact hno u (by simpa [A, B, U] using hUbetween)
  have hV_not_Ioo : ¬ tv ∈ Set.Ioo (0 : ℝ) 1 := by
    intro htv
    have hVbetween : Sbtw ℝ A V B := by
      rw [sbtw_iff_mem_image_Ioo_and_ne]
      exact ⟨⟨tv, htv, hV⟩, hAB⟩
    exact hno v (by simpa [A, B, V] using hVbetween)
  have hend_bounds : (tu ≤ 0 ∧ 1 ≤ tv) ∨ (tv ≤ 0 ∧ 1 ≤ tu) := by
    rcases lt_or_gt_of_ne htu_ne_tv with hlt | hgt
    · have htu_half : tu < (1 : ℝ) / 2 := by
        nlinarith [hhalf_param, hr.1, hr.2, hlt]
      have hhalf_tv : (1 : ℝ) / 2 < tv := by
        nlinarith [hhalf_param, hr.1, hr.2, hlt]
      left
      constructor
      · by_contra htu_pos_not
        exact hU_not_Ioo ⟨lt_of_not_ge htu_pos_not, by linarith⟩
      · by_contra htv_ge_not
        exact hV_not_Ioo ⟨by linarith, lt_of_not_ge htv_ge_not⟩
    · have htv_half : tv < (1 : ℝ) / 2 := by
        nlinarith [hhalf_param, hr.1, hr.2, hgt]
      have hhalf_tu : (1 : ℝ) / 2 < tu := by
        nlinarith [hhalf_param, hr.1, hr.2, hgt]
      right
      constructor
      · by_contra htv_pos_not
        exact hV_not_Ioo ⟨lt_of_not_ge htv_pos_not, by linarith⟩
      · by_contra htu_ge_not
        exact hU_not_Ioo ⟨by linarith, lt_of_not_ge htu_ge_not⟩
  let ra : ℝ := (0 - tu) / (tv - tu)
  let rb : ℝ := (1 - tu) / (tv - tu)
  have hden : tv - tu ≠ 0 := by
    intro h
    exact htu_ne_tv (by linarith)
  have hAuv : AffineMap.lineMap U V ra = A := by
    calc
      AffineMap.lineMap U V ra
          = AffineMap.lineMap
              (AffineMap.lineMap A B tu) (AffineMap.lineMap A B tv) ra := by
              rw [hU, hV]
      _ = AffineMap.lineMap A B ((1 - ra) * tu + ra * tv) := by
              rw [lineMap_lineMap_param_engine]
      _ = AffineMap.lineMap A B (0 : ℝ) := by
              congr 1
              dsimp [ra]
              field_simp [hden]
              ring
      _ = A := by ext <;> simp [AffineMap.lineMap_apply]
  have hBuv : AffineMap.lineMap U V rb = B := by
    calc
      AffineMap.lineMap U V rb
          = AffineMap.lineMap
              (AffineMap.lineMap A B tu) (AffineMap.lineMap A B tv) rb := by
              rw [hU, hV]
      _ = AffineMap.lineMap A B ((1 - rb) * tu + rb * tv) := by
              rw [lineMap_lineMap_param_engine]
      _ = AffineMap.lineMap A B (1 : ℝ) := by
              congr 1
              dsimp [rb]
              field_simp [hden]
              ring
      _ = B := by ext <;> simp [AffineMap.lineMap_apply]
  have hra : ra ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hend_bounds with h | h
    · dsimp [ra]
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith
    · dsimp [ra]
      constructor
      · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · exact div_le_one_of_ge (by linarith) (by linarith)
  have hrb : rb ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hend_bounds with h | h
    · dsimp [rb]
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith
    · dsimp [rb]
      constructor
      · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · exact div_le_one_of_ge (by linarith) (by linarith)
  constructor
  · exact ⟨ra, hra, by simpa [A, U, V] using hAuv⟩
  · exact ⟨rb, hrb, by simpa [B, U, V] using hBuv⟩





lemma minDistToSidesNotContaining_pos (m : ℝ × ℝ) :
    0 < minDistToSidesNotContaining D m := by
  classical
  unfold minDistToSidesNotContaining
  by_cases hne : (sideSegmentsNotContaining D m).Nonempty
  · rw [dif_pos hne]
    exact (Finset.lt_inf'_iff hne).mpr fun ij hij => by
      have hnot : m ∉ triSideSegment D ij := by
        have hij' :
            ij ∈ Finset.univ.filter (fun ij => m ∉ triSideSegment D ij) := by
          simpa [sideSegmentsNotContaining] using hij
        exact (Finset.mem_filter.mp hij').2
      exact ((triSideSegment_closed D ij).notMem_iff_infDist_pos
        (triSideSegment_nonempty D ij)).mp hnot
  · rw [dif_neg hne]
    norm_num

lemma dist_lt_minDistToSidesNotContaining_not_mem
    {m x : ℝ × ℝ} {ij : Fin D.n × Fin 3}
    (hij : m ∉ triSideSegment D ij)
    (hdist : dist m x < minDistToSidesNotContaining D m) :
    x ∉ triSideSegment D ij := by
  classical
  unfold minDistToSidesNotContaining at hdist
  by_cases hne : (sideSegmentsNotContaining D m).Nonempty
  · have hijmem : ij ∈ sideSegmentsNotContaining D m := by
      simp [sideSegmentsNotContaining, hij]
    rw [dif_pos hne] at hdist
    have hle :
        (sideSegmentsNotContaining D m).inf' hne
          (fun ij => Metric.infDist m (triSideSegment D ij)) ≤
        Metric.infDist m (triSideSegment D ij) :=
      Finset.inf'_le (fun ij => Metric.infDist m (triSideSegment D ij)) hijmem
    exact Metric.notMem_of_dist_lt_infDist (hdist.trans_le hle)
  · have hijmem : ij ∈ sideSegmentsNotContaining D m := by
      simp [sideSegmentsNotContaining, hij]
    exact (hne ⟨ij, hijmem⟩).elim

lemma signedOpenHalfDisk_disjoint_frontier_triHull
    {i₀ k : Fin D.n} {a b : D.vtx} {ε σ : ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hεle : ε ≤ minDistToSidesNotContaining D
      (midpoint ℝ (D.coord a) (D.coord b))) :
    Disjoint
      (signedOpenHalfDisk (D.coord a) (D.coord b)
        (midpoint ℝ (D.coord a) (D.coord b)) ε σ)
      (frontier (triHull D k)) := by
  rw [Set.disjoint_left]
  intro x hxH hxFront
  let m := midpoint ℝ (D.coord a) (D.coord b)
  rcases exists_triSide_of_mem_frontier_triHull D hxFront with ⟨j, hxSide⟩
  by_cases hmSide : m ∈ triSideSegment D (k, j)
  · have hzero :
        doubleArea (D.coord a) (D.coord b) x = 0 :=
      doubleArea_eq_zero_of_mem_triSideSegment_containing_atomic_midpoint
        D h₀ (by simpa [m] using hmSide) hxSide
    have hpos : 0 < σ * doubleArea (D.coord a) (D.coord b) x := hxH.2
    rw [hzero, mul_zero] at hpos
    linarith
  · have hdist : dist m x < minDistToSidesNotContaining D m := by
      have hdist' : dist m x < ε := by
        simpa [dist_comm, m] using hxH.1
      exact hdist'.trans_le (by simpa [m] using hεle)
    exact dist_lt_minDistToSidesNotContaining_not_mem D hmSide hdist hxSide

lemma signedOpenHalfDisk_midpoint_nonempty
    {A B : ℝ × ℝ} (hAB : A ≠ B) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    (signedOpenHalfDisk A B (midpoint ℝ A B) ε σ).Nonempty := by
  let n : ℝ × ℝ := (-(B.2 - A.2), B.1 - A.1)
  have hn_ne : n ≠ 0 := by
    intro hn
    apply hAB
    have h₁ : B.1 - A.1 = 0 := by
      have h := congrArg Prod.snd hn
      simpa [n] using h
    have h₂ : B.2 - A.2 = 0 := by
      have h := congrArg Prod.fst hn
      simpa [n] using neg_eq_zero.mp h
    ext <;> linarith
  have hn_norm_pos : 0 < ‖n‖ := norm_pos_iff.mpr hn_ne
  let δ : ℝ := ε / (2 * ‖n‖)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδnorm : δ * ‖n‖ = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hn_norm_pos]
  have hsq_pos : 0 < (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 := by
    by_contra hnot
    have hle : (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 ≤ 0 := le_of_not_gt hnot
    have h₁ : B.1 - A.1 = 0 := by
      nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]
    have h₂ : B.2 - A.2 = 0 := by
      nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]
    exact hAB (by ext <;> linarith)
  rcases hσ with rfl | rfl
  · let x : ℝ × ℝ := midpoint ℝ A B + δ • n
    refine ⟨x, ?_⟩
    constructor
    · have hdist : dist x (midpoint ℝ A B) = δ * ‖n‖ := by
        rw [dist_eq_norm]
        have hxsub : x - midpoint ℝ A B = δ • n := by
          ext <;> simp [x]
        rw [hxsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      rw [hdist, hδnorm]
      linarith
    · have harea :
          doubleArea A B x =
            δ * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
        unfold doubleArea
        simp [x, n, midpoint, AffineMap.lineMap_apply, Prod.smul_def]
        ring
      rw [harea]
      positivity
  · let x : ℝ × ℝ := midpoint ℝ A B - δ • n
    refine ⟨x, ?_⟩
    constructor
    · have hdist : dist x (midpoint ℝ A B) = δ * ‖n‖ := by
        rw [dist_eq_norm]
        have hxsub : x - midpoint ℝ A B = (-δ) • n := by
          ext <;> simp [x]
        rw [hxsub, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
        ring
      rw [hdist, hδnorm]
      linarith
    · have harea :
          doubleArea A B x =
            -δ * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
        unfold doubleArea
        simp [x, n, midpoint, AffineMap.lineMap_apply, Prod.smul_def]
        ring
      rw [harea]
      nlinarith [hδpos, hsq_pos]

lemma midpoint_mem_closure_signedOpenHalfDisk
    {A B : ℝ × ℝ} (hAB : A ≠ B) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    midpoint ℝ A B ∈ closure (signedOpenHalfDisk A B (midpoint ℝ A B) ε σ) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  let ε' : ℝ := min ε η
  have hε' : 0 < ε' := by
    dsimp [ε']
    exact lt_min hε hη
  rcases signedOpenHalfDisk_midpoint_nonempty (A := A) (B := B) hAB hε' hσ with
    ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · exact ⟨lt_of_lt_of_le hx.1 (by dsimp [ε']; exact min_le_left _ _), hx.2⟩
  · rw [dist_comm]
    exact lt_of_lt_of_le hx.1 (by dsimp [ε']; exact min_le_right _ _)

lemma midpoint_mem_frontier_of_signedOpenHalfDisk_subset_interior
    {i₀ t : Fin D.n} {a b : D.vtx} {ε σ : ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hsub : signedOpenHalfDisk (D.coord a) (D.coord b)
        (midpoint ℝ (D.coord a) (D.coord b)) ε σ ⊆ interior (triHull D t)) :
    midpoint ℝ (D.coord a) (D.coord b) ∈ frontier (triHull D t) := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have hab : a ≠ b := ne_of_mk_mem_triAtomicEdges D h₀
  have hAB : D.coord a ≠ D.coord b := fun h => hab (D.coord_inj h)
  have hmClosureH :
      m ∈ closure (signedOpenHalfDisk (D.coord a) (D.coord b) m ε σ) := by
    simpa [m] using
      midpoint_mem_closure_signedOpenHalfDisk
        (A := D.coord a) (B := D.coord b) hAB hε hσ
  have hHhull :
      signedOpenHalfDisk (D.coord a) (D.coord b) m ε σ ⊆ triHull D t :=
    hsub.trans interior_subset
  have hmClosureHull : m ∈ closure (triHull D t) :=
    closure_mono hHhull hmClosureH
  have hmHull : m ∈ triHull D t := by
    simpa [(triHull_closed D t).closure_eq] using hmClosureHull
  refine (mem_frontier_iff_notMem_interior hmHull).mpr ?_
  intro hmInt
  have hmFront₀ : m ∈ frontier (triHull D i₀) := by
    simpa [m] using midpoint_mem_frontier_triHull_of_mem_triAtomicEdges D h₀
  by_cases hti : t = i₀
  · subst t
    exact Set.disjoint_left.mp disjoint_interior_frontier hmInt hmFront₀
  · have hnhds : interior (triHull D t) ∈ 𝓝 m :=
      isOpen_interior.mem_nhds hmInt
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ρ, hρ, hball⟩
    rcases exists_incidentSideWitness D h₀ with ⟨W₀, _⟩
    have hpq : W₀.p ≠ W₀.q := by
      intro hpq
      exact W₀.hnd (by simp [hpq, doubleArea])
    have hmSide :
        m ∈ openSegment ℝ (D.coord W₀.p) (D.coord W₀.q) := by
      simpa [m] using
        midpoint_mem_openSegment_of_mem_sideAtomicEdges D hpq W₀.hmem
    have hmr : m ≠ D.coord W₀.r :=
      (atomicEdge_midpoint_ne_vertex D i₀ h₀ W₀.r).symm
    rcases exists_openSegment_point_dist_lt hmr hρ with ⟨x, hxseg, hxdist⟩
    have hx₀ : x ∈ interior (triHull D i₀) := by
      have hxint :=
        openSegment_edge_to_opposite_subset_interior_convexHull
          (D.coord W₀.p) (D.coord W₀.q) (D.coord W₀.r) m
          W₀.hnd hmSide hxseg
      simpa [W₀.hHull] using hxint
    have hxt : x ∈ interior (triHull D t) := by
      exact hball hxdist
    exact Set.disjoint_left.mp (D.disjoint_int t i₀ hti) hxt hx₀

lemma incident_of_midpoint_mem_frontier_triHull
    {i₀ t : Fin D.n} {a b : D.vtx}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hmFront : midpoint ℝ (D.coord a) (D.coord b) ∈ frontier (triHull D t)) :
    t ∈ incidentTris D s(a, b) := by
  rcases exists_triSide_of_mem_frontier_triHull D hmFront with ⟨j, hmSide⟩
  have hmOpen :
      midpoint ℝ (D.coord a) (D.coord b) ∈
        openSegment ℝ (D.coord (triSideP D t j)) (D.coord (triSideQ D t j)) :=
    midpoint_mem_openSegment_of_mem_triSideSegment_of_atomic D h₀ hmSide
  have hPmem :
      D.coord (triSideP D t j) ∈ triSideSegment D (t, j) := by
    unfold triSideSegment
    exact left_mem_segment ℝ _ _
  have hQmem :
      D.coord (triSideQ D t j) ∈ triSideSegment D (t, j) := by
    unfold triSideSegment
    exact right_mem_segment ℝ _ _
  have hPline :
      doubleArea (D.coord a) (D.coord b) (D.coord (triSideP D t j)) = 0 :=
    doubleArea_eq_zero_of_mem_triSideSegment_containing_atomic_midpoint D h₀ hmSide hPmem
  have hQline :
      doubleArea (D.coord a) (D.coord b) (D.coord (triSideQ D t j)) = 0 :=
    doubleArea_eq_zero_of_mem_triSideSegment_containing_atomic_midpoint D h₀ hmSide hQmem
  have hpq : triSideP D t j ≠ triSideQ D t j := by
    intro hpq
    exact triSide_nondeg D t j (by simp [hpq, doubleArea])
  have hon :
      OnSide D (triSideP D t j) (triSideQ D t j) a ∧
        OnSide D (triSideP D t j) (triSideQ D t j) b :=
    endpoints_onSide_of_midpoint_openSegment_of_collinear_no_sbtw D h₀ hpq hmOpen
      hPline hQline
  have hab : a ≠ b := ne_of_mk_mem_triAtomicEdges D h₀
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
    fun z => not_sbtw_of_mem_triAtomicEdges_engine D h₀
  have hside :
      s(a, b) ∈ sideAtomicEdges D (triSideP D t j) (triSideQ D t j) :=
    mem_sideAtomicEdges_of_onSide_no_sbtw_engine D hpq hon.1 hon.2 hab hno
  have htri : s(a, b) ∈ triAtomicEdges D t := by
    fin_cases j
    · rw [mem_triAtomicEdges_iff]
      exact Or.inl (by simpa [triSideP, triSideQ] using hside)
    · rw [mem_triAtomicEdges_iff]
      exact Or.inr <| Or.inl (by simpa [triSideP, triSideQ] using hside)
    · rw [mem_triAtomicEdges_iff]
      exact Or.inr <| Or.inr (by simpa [triSideP, triSideQ] using hside)
  simpa [incidentTris] using htri

lemma incidentOppSign_eq_of_signedOpenHalfDisk_subset_interior
    {i₀ t : Fin D.n} {a b : D.vtx} {ε σ : ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hsub : signedOpenHalfDisk (D.coord a) (D.coord b)
        (midpoint ℝ (D.coord a) (D.coord b)) ε σ ⊆ interior (triHull D t))
    (ht : t ∈ incidentTris D s(a, b)) :
    incidentOppSign D a b t = σ := by
  let A := D.coord a
  let B := D.coord b
  let m := midpoint ℝ A B
  have hab : a ≠ b := ne_of_mk_mem_triAtomicEdges D h₀
  have hAB : A ≠ B := fun h => hab (D.coord_inj h)
  rcases signedOpenHalfDisk_midpoint_nonempty (A := A) (B := B) hAB hε hσ with
    ⟨x, hxH⟩
  have htri : s(a, b) ∈ triAtomicEdges D t := by
    simpa [incidentTris] using ht
  rcases exists_incidentSideWitness D htri with ⟨W, _⟩
  have hxInt :
      x ∈ interior (convexHull ℝ
        ({D.coord W.p, D.coord W.q, D.coord W.r} : Set (ℝ × ℝ))) := by
    simpa [A, B, m, W.hHull] using hsub hxH
  have hpqProd :
      0 < doubleArea (D.coord W.p) (D.coord W.q) x *
        doubleArea (D.coord W.p) (D.coord W.q) (D.coord W.r) :=
    doubleArea_edge_mul_pos_of_mem_interior_convexHull
      (D.coord W.p) (D.coord W.q) (D.coord W.r) x W.hnd hxInt
  have hon := endpoints_onSide_of_mem_sideAtomicEdges D W.hmem
  obtain ⟨ta, _hta, haeq⟩ := hon.1
  obtain ⟨tb, _htb, hbeq⟩ := hon.2
  have hxArea :
      doubleArea A B x =
        (tb - ta) * doubleArea (D.coord W.p) (D.coord W.q) x := by
    dsimp [A, B]
    rw [← haeq, ← hbeq]
    exact doubleArea_lineMap_lineMap_left (D.coord W.p) (D.coord W.q) x ta tb
  have hRArea :
      doubleArea A B (D.coord W.r) =
        (tb - ta) * doubleArea (D.coord W.p) (D.coord W.q) (D.coord W.r) := by
    dsimp [A, B]
    rw [← haeq, ← hbeq]
    exact doubleArea_lineMap_lineMap_left (D.coord W.p) (D.coord W.q) (D.coord W.r) ta tb
  have htab : tb - ta ≠ 0 := by
    intro hzero
    apply hAB
    have htbta : tb = ta := by linarith
    dsimp [A, B]
    rw [← haeq, ← hbeq, htbta]
  have htabSq : 0 < (tb - ta) * (tb - ta) := by
    nlinarith [sq_pos_of_ne_zero htab]
  have hABProd :
      0 < doubleArea A B x * doubleArea A B (D.coord W.r) := by
    rw [hxArea, hRArea]
    have hfactor :
        ((tb - ta) * doubleArea (D.coord W.p) (D.coord W.q) x) *
          ((tb - ta) * doubleArea (D.coord W.p) (D.coord W.q) (D.coord W.r)) =
        ((tb - ta) * (tb - ta)) *
          (doubleArea (D.coord W.p) (D.coord W.q) x *
            doubleArea (D.coord W.p) (D.coord W.q) (D.coord W.r)) := by
      ring
    rw [hfactor]
    exact mul_pos htabSq hpqProd
  rw [W.hopp]
  rcases hσ with rfl | rfl
  · have hxpos : 0 < doubleArea A B x := by
      simpa [A, B, m] using hxH.2
    have hRpos : 0 < doubleArea A B (D.coord W.r) := by
      rcases mul_pos_iff.mp hABProd with hsame | hsame
      · exact hsame.2
      · linarith
    simp [realSign, A, B, hRpos]
  · have hxneg : doubleArea A B x < 0 := by
      nlinarith [hxH.2]
    have hRneg : doubleArea A B (D.coord W.r) < 0 := by
      rcases mul_pos_iff.mp hABProd with hsame | hsame
      · linarith
      · exact hsame.2
    simp [realSign, A, B, not_lt_of_ge hRneg.le]

open scoped Classical in
lemma exists_incident_of_signedOpenHalfDisk_subset_unitSquare
    {i₀ : Fin D.n} {a b : D.vtx} {ε σ : ℝ}
    (h₀ : s(a, b) ∈ triAtomicEdges D i₀)
    (hε : 0 < ε)
    (hεle : ε ≤ minDistToSidesNotContaining D
      (midpoint ℝ (D.coord a) (D.coord b)))
    (hσ : σ = 1 ∨ σ = -1)
    (hsubSq : signedOpenHalfDisk (D.coord a) (D.coord b)
        (midpoint ℝ (D.coord a) (D.coord b)) ε σ ⊆ unitSquareSet) :
    ∃ t ∈ incidentTris D s(a, b), incidentOppSign D a b t = σ := by
  classical
  let A := D.coord a
  let B := D.coord b
  let m := midpoint ℝ A B
  let H := signedOpenHalfDisk A B m ε σ
  have hab : a ≠ b := ne_of_mk_mem_triAtomicEdges D h₀
  have hAB : A ≠ B := fun h => hab (D.coord_inj h)
  have hHne : H.Nonempty := by
    simpa [H, A, B, m] using
      signedOpenHalfDisk_midpoint_nonempty (A := A) (B := B) hAB hε hσ
  have hfront : ∀ k : Fin D.n, Disjoint H (frontier (triHull D k)) := by
    intro k
    simpa [H, A, B, m] using
      signedOpenHalfDisk_disjoint_frontier_triHull D (k := k) h₀ hεle
  have hpre : IsPreconnected H := by
    simpa [H, A, B, m] using isPreconnected_signedOpenHalfDisk A B m
  have hsubSq' : H ⊆ unitSquareSet := by
    simpa [H, A, B, m] using hsubSq
  rcases exists_triHull_interior_of_preconnected D H hpre hHne hsubSq' hfront with
    ⟨t, hsubInt⟩
  have hmFront :
      m ∈ frontier (triHull D t) := by
    simpa [A, B, m] using
      midpoint_mem_frontier_of_signedOpenHalfDisk_subset_interior D h₀ hε hσ
        (by simpa [H, A, B, m] using hsubInt)
  have ht : t ∈ incidentTris D s(a, b) := by
    simpa [A, B, m] using
      incident_of_midpoint_mem_frontier_triHull D h₀ hmFront
  have hsign : incidentOppSign D a b t = σ :=
    incidentOppSign_eq_of_signedOpenHalfDisk_subset_interior D h₀ hε hσ
      (by simpa [H, A, B, m] using hsubInt) ht
  exact ⟨t, ht, hsign⟩

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
lemma incidentOppSign_image_subset_pair (a b : D.vtx) :
    (incidentTris D s(a, b)).image (incidentOppSign D a b) ⊆ ({1, -1} : Finset ℝ) := by
  classical
  intro σ hσ
  rw [Finset.mem_image] at hσ
  rcases hσ with ⟨i, _hi, rfl⟩
  rcases incidentOppSign_eq_one_or_neg_one D a b i with h | h
  · simp [h]
  · simp [h]

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
lemma incidentTris_card_eq_two_of_realize_both {a b : D.vtx}
    (hpos : 1 ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b))
    (hneg : -1 ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b)) :
    (incidentTris D s(a, b)).card = 2 := by
  classical
  let I := (incidentTris D s(a, b)).image (incidentOppSign D a b)
  have hsub : I ⊆ ({1, -1} : Finset ℝ) := incidentOppSign_image_subset_pair D a b
  have hpair_subset : ({1, -1} : Finset ℝ) ⊆ I := by
    intro σ hσ
    simp at hσ
    rcases hσ with rfl | rfl
    · exact hpos
    · exact hneg
  have hI : I = ({1, -1} : Finset ℝ) :=
    Finset.Subset.antisymm hsub hpair_subset
  rw [incidentTris_card_eq_image_card D a b]
  change I.card = 2
  rw [hI]
  norm_num



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
    (he : IsAtomicEdge D e) (hint : ¬ OnSquareBoundary D e) :
    Even (atomicMult D e) := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      rcases he with ⟨i₀, h₀⟩
      let A := D.coord a
      let B := D.coord b
      let m := midpoint ℝ A B
      have hsegSq : segment ℝ A B ⊆ unitSquareSet := by
        simpa [A, B] using segment_subset_unitSquare_of_mem_triAtomicEdges D h₀
      have hmSq : m ∈ unitSquareSet := by
        exact hsegSq (by simpa [m] using
          midpoint_mem_segment (𝕜 := ℝ) A B)
      have hmNotFront : m ∉ frontier unitSquareSet := by
        intro hmFront
        have hsegFront : segment ℝ A B ⊆ frontier unitSquareSet :=
          segment_subset_frontier_unitSquare_of_midpoint_mem_frontier hsegSq hmFront
        have hbd : OnSquareBoundary D s(a, b) := by
          have hsym : Symmetric (fun p q : D.vtx =>
              segment ℝ (D.coord p) (D.coord q) ⊆
                frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1))) := by
            intro p q hpq x hx
            exact hpq (by simpa [segment_symm] using hx)
          simpa [OnSquareBoundary, unitSquareSet, A, B] using
            (Sym2.fromRel_prop (sym := hsym) (a := a) (b := b)).mpr hsegFront
        exact hint hbd
      have hmInt : m ∈ interior unitSquareSet := by
        by_contra hmNotInt
        exact hmNotFront ((mem_frontier_iff_notMem_interior hmSq).mpr hmNotInt)
      have hnhdsInt : interior unitSquareSet ∈ 𝓝 m :=
        isOpen_interior.mem_nhds hmInt
      have hnhdsSq : unitSquareSet ∈ 𝓝 m :=
        Filter.mem_of_superset hnhdsInt interior_subset
      rcases Metric.mem_nhds_iff.mp hnhdsSq with ⟨ρ, hρ, hball⟩
      let μ := minDistToSidesNotContaining D m
      let ε : ℝ := min (ρ / 2) (μ / 2)
      have hμ : 0 < μ := by
        simpa [μ, A, B, m] using minDistToSidesNotContaining_pos D m
      have hε : 0 < ε := by
        dsimp [ε]
        exact lt_min (by positivity) (by positivity)
      have hεleμ : ε ≤ μ := by
        calc
          ε ≤ μ / 2 := by dsimp [ε]; exact min_le_right _ _
          _ ≤ μ := by linarith
      have hsubH : ∀ σ : ℝ,
          signedOpenHalfDisk A B m ε σ ⊆ unitSquareSet := by
        intro σ x hx
        have hxε : dist x m < ε := hx.1
        have hερ : ε ≤ ρ := by
          calc
            ε ≤ ρ / 2 := by dsimp [ε]; exact min_le_left _ _
            _ ≤ ρ := by linarith
        exact hball (by simpa [Metric.mem_ball] using hxε.trans_le hερ)
      rcases exists_incident_of_signedOpenHalfDisk_subset_unitSquare D h₀ hε
          (by simpa [A, B, m, μ] using hεleμ) (Or.inl rfl)
          (by simpa [A, B, m] using hsubH 1) with
        ⟨tpos, htpos, hspos⟩
      rcases exists_incident_of_signedOpenHalfDisk_subset_unitSquare D h₀ hε
          (by simpa [A, B, m, μ] using hεleμ) (Or.inr rfl)
          (by simpa [A, B, m] using hsubH (-1)) with
        ⟨tneg, htneg, hsneg⟩
      have hpos :
          1 ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b) := by
        rw [Finset.mem_image]
        exact ⟨tpos, htpos, hspos⟩
      have hneg :
          -1 ∈ (incidentTris D s(a, b)).image (incidentOppSign D a b) := by
        rw [Finset.mem_image]
        exact ⟨tneg, htneg, hsneg⟩
      have hcard : (incidentTris D s(a, b)).card = 2 :=
        incidentTris_card_eq_two_of_realize_both D hpos hneg
      rw [atomicMult_eq_incidentTris_card D s(a, b), hcard]
      norm_num
