-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.isAtomic_of_mem_squareSideAtomicEdges
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:51:02.845704+00:00
-- url     : https://prove2.me/submissions/5db21135-7027-474a-9d46-05c4a3437d96

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

























lemma triHullLocal_subset_unitSquare (i : Fin D.n) :
    triHullLocal D i ⊆ unitSquareSetLocal := by
  intro x hx
  have hxUnion :
      x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
    exact Set.mem_iUnion.mpr ⟨i, by simpa [triHullLocal] using hx⟩
  rw [D.cover] at hxUnion
  simpa [unitSquareSetLocal] using hxUnion

lemma not_mem_interior_triHull_of_mem_frontier_unitSquare {x : ℝ × ℝ}
    (hx : x ∈ frontier unitSquareSetLocal) (i : Fin D.n) :
    x ∉ interior (triHullLocal D i) := by
  have hxSq : x ∈ unitSquareSetLocal := by
    have hxf :
        x ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
      simpa [unitSquareSetLocal] using hx
    rw [frontier_unitSquare] at hxf
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using
      ⟨⟨hxf.1, hxf.2.2.1⟩, ⟨hxf.2.1, hxf.2.2.2.1⟩⟩
  have hxNotInterior : x ∉ interior unitSquareSetLocal :=
    (mem_frontier_iff_notMem_interior hxSq).mp hx
  intro hxTri
  exact hxNotInterior (interior_mono (triHullLocal_subset_unitSquare D i) hxTri)

open scoped Classical in
lemma mem_sideInteriorChain_iff_local {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]

open scoped Classical in
lemma sideInteriorChain_nodup_local (p q : D.vtx) :
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

lemma left_not_mem_sideInteriorChain_local (p q : D.vtx) :
    p ∉ sideInteriorChain D p q := by
  intro hp
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hp |>.2.1 rfl

lemma right_not_mem_sideInteriorChain_local (p q : D.vtx) :
    q ∉ sideInteriorChain D p q := by
  intro hq
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hq |>.2.2 rfl

lemma sideChain_nodup_local {p q : D.vtx} (hpq : p ≠ q) :
    (p :: sideInteriorChain D p q ++ [q]).Nodup := by
  classical
  rw [List.nodup_append, List.nodup_cons]
  refine ⟨⟨left_not_mem_sideInteriorChain_local D p q,
    sideInteriorChain_nodup_local D p q⟩, List.nodup_singleton q, ?_⟩
  intro a ha b hb hab
  rw [List.mem_cons] at ha
  rw [List.mem_singleton] at hb
  subst b
  rcases ha with rfl | ha
  · exact hpq hab
  · exact right_not_mem_sideInteriorChain_local D p q (hab ▸ ha)

lemma endpoints_mem_of_mem_consecutiveEdges_local {α : Type*} {l : List α} {a b : α}
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



lemma not_diag_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
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

lemma ne_of_mk_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ≠ b := by
  intro hab
  subst b
  exact not_diag_mem_consecutiveEdges_of_nodup_local hnd a h

lemma onSide_left_local (p q : D.vtx) : OnSide D p q p := by
  exact wbtw_self_left (R := ℝ) (D.coord p) (D.coord q)

lemma onSide_right_local (p q : D.vtx) : OnSide D p q q := by
  exact wbtw_self_right (R := ℝ) (D.coord p) (D.coord q)

lemma sideInteriorChain_onSide_local {p q w : D.vtx}
    (hw : w ∈ sideInteriorChain D p q) : OnSide D p q w :=
  (mem_sideInteriorChain_iff_local (D := D)).mp hw |>.1

lemma onSide_of_mem_sideChain_local {p q w : D.vtx}
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) : OnSide D p q w := by
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_cons] at hw
    rcases hw with hwp | hw
    · rw [hwp]
      exact onSide_left_local D p q
    · exact sideInteriorChain_onSide_local D hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact onSide_right_local D p q

lemma endpoints_onSide_of_mem_sideAtomicEdges_local {p q a b : D.vtx}
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    OnSide D p q a ∧ OnSide D p q b := by
  unfold sideAtomicEdges at h
  have hend := endpoints_mem_of_mem_consecutiveEdges_local h
  exact ⟨onSide_of_mem_sideChain_local D hend.1,
    onSide_of_mem_sideChain_local D hend.2⟩

lemma ne_of_mk_mem_sideAtomicEdges_local {p q a b : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) : a ≠ b := by
  unfold sideAtomicEdges at h
  exact ne_of_mk_mem_consecutiveEdges_of_nodup_local (sideChain_nodup_local D hpq) h



lemma sideParam_spec_of_onSide {p q w : D.vtx} (hpq : p ≠ q)
    (hw : OnSide D p q w) :
    sideParam D p q w ∈ Set.Icc (0 : ℝ) 1 ∧
      AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q w) = D.coord w := by
  unfold OnSide at hw
  obtain ⟨t, ht, htw⟩ := hw
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_pos hx]
      have hxf := congrArg Prod.fst htw
      simp [AffineMap.lineMap_apply] at hxf
      field_simp [hx]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw
  · have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_neg hx]
      have hyf := congrArg Prod.snd htw
      simp [AffineMap.lineMap_apply] at hyf
      field_simp [hy]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw

lemma sideParam_left_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q p = 0 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
  · have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    simp [hx]

lemma sideParam_right_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q q = 1 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · rw [if_pos hx]
    field_simp [hx]
  · rw [if_neg hx]
    have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    field_simp [hy]

open scoped Classical in
lemma sideInteriorChain_pairwise_sideParam (p q : D.vtx) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (sideInteriorChain D p q) := by
  classical
  unfold sideInteriorChain
  exact List.pairwise_insertionSort _ _

open scoped Classical in
lemma sideChain_pairwise_sideParam {p q : D.vtx} (hpq : p ≠ q) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (p :: sideInteriorChain D p q ++ [q]) := by
  classical
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      rw [sideParam_left_eq_local (D := D) hpq]
      exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D hx)).1.1
    · exact sideInteriorChain_pairwise_sideParam D p q
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb, sideParam_right_eq_local (D := D) hpq]
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [sideParam_left_eq_local (D := D) hpq]
      norm_num
    · exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D ha)).1.2

lemma not_sideParam_between_of_mem_consecutiveEdges_pairwise
    {α : Type*} {f : α → ℝ} :
    ∀ {l : List α} {a b w : α},
      List.Pairwise (fun x y => f x ≤ f y) l →
      s(a, b) ∈ consecutiveEdges l →
      w ∈ l →
      ¬ (f a < f w ∧ f w < f b)
  | [], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | [_x], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | x :: y :: rest, a, b, w, hpair, h, hw => by
      rw [List.pairwise_cons] at hpair
      have hxy0 : f x ≤ f y := hpair.1 y (by simp)
      rw [consecutiveEdges, List.mem_cons] at h
      rcases h with hfirst | htail
      · rw [Sym2.eq_iff] at hfirst
        rcases hfirst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [List.mem_cons] at hw
          intro hbetween
          rcases hw with rfl | hw
          · linarith
          · rw [List.mem_cons] at hw
            rcases hw with rfl | hwrest
            · linarith
            · have hyw : f b ≤ f w := by
                have htailPair := hpair.2
                rw [List.pairwise_cons] at htailPair
                exact htailPair.1 w hwrest
              linarith
        · intro hbetween
          linarith
      · rw [List.mem_cons] at hw
        rcases hw with rfl | hwtail
        · have hend := endpoints_mem_of_mem_consecutiveEdges_local htail
          have hxa : f w ≤ f a := hpair.1 a (by simpa using hend.1)
          intro hbetween
          linarith
        · exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
            hpair.2 htail hwtail

lemma not_sideParam_between_of_mem_sideAtomicEdges {p q a b w : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q)
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) :
    ¬ (sideParam D p q a < sideParam D p q w ∧
      sideParam D p q w < sideParam D p q b) := by
  unfold sideAtomicEdges at h
  exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
    (sideChain_pairwise_sideParam (D := D) hpq) h hw

lemma mem_consecutiveEdges_of_pairwise_no_between
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
            (mem_consecutiveEdges_of_pairwise_no_between
              (l := y :: ys) (f := f) (P := P)
              htail_nd htail_all hinj htail_pair ha_tail hb_tail hlt
              (fun z hz => hno z (by simp [hz])))

lemma sideParam_injective_onSide_local {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hparam : sideParam D p q a = sideParam D p q b) :
    a = b := by
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  apply D.coord_inj
  calc
    D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q a) :=
      ha_spec.2.symm
    _ = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q b) := by
      rw [hparam]
    _ = D.coord b := hb_spec.2

lemma sideParam_eq_of_lineMap_local {p q w : D.vtx} (hpq : p ≠ q) {t : ℝ}
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

lemma lineMap_param_injective_local {p q : D.vtx} (hpq : p ≠ q) {t u : ℝ}
    (h : AffineMap.lineMap (D.coord p) (D.coord q) t =
      AffineMap.lineMap (D.coord p) (D.coord q) u) :
    t = u := by
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro hcoord
    exact hpq (D.coord_inj hcoord.symm)
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · have hfst := congrArg Prod.fst h
    simp [AffineMap.lineMap_apply] at hfst
    rcases hfst with htu | hzero
    · exact htu
    · exact False.elim (hx (by linarith))
  · have hxeq : (D.coord q).1 = (D.coord p).1 := by exact not_not.mp hx
    have hy : (D.coord q).2 - (D.coord p).2 ≠ 0 := by
      intro hzero
      apply hcoord_ne
      ext
      · exact hxeq
      · linarith
    have hsnd := congrArg Prod.snd h
    simp [AffineMap.lineMap_apply] at hsnd
    rcases hsnd with htu | hzero
    · exact htu
    · exact False.elim (hy hzero)

lemma onSide_of_sideParam_interval_local {p q u v a : D.vtx} (hpq : p ≠ q)
    (hu : OnSide D p q u) (hv : OnSide D p q v) (ha : OnSide D p q a)
    (hlt : sideParam D p q u < sideParam D p q v)
    (hua : sideParam D p q u ≤ sideParam D p q a)
    (hav : sideParam D p q a ≤ sideParam D p q v) :
    OnSide D u v a := by
  let tu := sideParam D p q u
  let tv := sideParam D p q v
  let ta := sideParam D p q a
  have hu_spec := sideParam_spec_of_onSide (D := D) hpq hu
  have hv_spec := sideParam_spec_of_onSide (D := D) hpq hv
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hden : tv - tu ≠ 0 := by
    dsimp [tu, tv]
    linarith
  have hden_pos : 0 < tv - tu := by
    dsimp [tu, tv]
    linarith
  let r : ℝ := (ta - tu) / (tv - tu)
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ), segment_eq_image_lineMap]
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · dsimp [r, tu, tv, ta]
    exact div_nonneg (sub_nonneg.mpr hua) (le_of_lt hden_pos)
  · dsimp [r, tu, tv, ta]
    rw [div_le_one hden_pos]
    linarith
  · calc
      AffineMap.lineMap (D.coord u) (D.coord v) r
          = AffineMap.lineMap
              (AffineMap.lineMap (D.coord p) (D.coord q) tu)
              (AffineMap.lineMap (D.coord p) (D.coord q) tv) r := by
              rw [hu_spec.2, hv_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * tu + r * tv) := by
              ext <;> simp [AffineMap.lineMap_apply] <;> ring
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ta := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord a := ha_spec.2

lemma mem_sideChain_of_onSide_local {p q w : D.vtx}
    (hw : OnSide D p q w) :
    w ∈ p :: sideInteriorChain D p q ++ [q] := by
  by_cases hwp : w = p
  · simp [hwp]
  by_cases hwq : w = q
  · simp [hwq]
  have hwint : w ∈ sideInteriorChain D p q := by
    rw [mem_sideInteriorChain_iff_local]
    exact ⟨hw, hwp, hwq⟩
  simp [hwint]

lemma lineMap_lineMap_param (P Q : ℝ × ℝ) (ta tb r : ℝ) :
    AffineMap.lineMap
        (AffineMap.lineMap P Q ta) (AffineMap.lineMap P Q tb) r =
      AffineMap.lineMap P Q ((1 - r) * ta + r * tb) := by
  ext <;> simp [AffineMap.lineMap_apply] <;> ring

lemma sbtw_of_sideParam_between_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (haz : sideParam D p q a < sideParam D p q z)
    (hzb : sideParam D p q z < sideParam D p q b) :
    Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
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
              rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
              rw [lineMap_lineMap_param]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord z := hz_spec.2
  · intro hab
    have habv : a = b := D.coord_inj hab
    subst b
    linarith

lemma sideParam_between_of_sbtw_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (hs : Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b) ∨
      (sideParam D p q b < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q a) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  rcases hs.mem_image_Ioo with ⟨r, hr, hzr⟩
  have hz_param : tz = (1 - r) * ta + r * tb := by
    dsimp [tz]
    apply sideParam_eq_of_lineMap_local D hpq
    calc
      D.coord z = AffineMap.lineMap (D.coord a) (D.coord b) r := hzr.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
            rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
            rw [lineMap_lineMap_param]
  have hne_param : ta ≠ tb := by
    intro htab
    have hcoord : D.coord a = D.coord b := by
      calc
        D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := ha_spec.2.symm
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tb := by rw [htab]
        _ = D.coord b := hb_spec.2
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

lemma mem_sideAtomicEdges_of_onSide_no_sideParam_between
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hlt : sideParam D p q a < sideParam D p q b)
    (hno : ∀ z : D.vtx, OnSide D p q z →
      ¬ (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  let chain := p :: sideInteriorChain D p q ++ [q]
  have ha_mem : a ∈ chain := mem_sideChain_of_onSide_local (D := D) ha
  have hb_mem : b ∈ chain := mem_sideChain_of_onSide_local (D := D) hb
  have hall : ∀ x, x ∈ chain → OnSide D p q x := by
    intro x hx
    exact onSide_of_mem_sideChain_local D hx
  unfold sideAtomicEdges
  exact mem_consecutiveEdges_of_pairwise_no_between
    (l := chain) (f := sideParam D p q) (P := fun x => OnSide D p q x)
    (sideChain_nodup_local D hpq) hall
    (fun x y hx hy hxy => sideParam_injective_onSide_local D hpq hx hy hxy)
    (sideChain_pairwise_sideParam (D := D) hpq) ha_mem hb_mem hlt
    (fun z hz => hno z (hall z hz))

lemma mem_sideAtomicEdges_of_onSide_no_sbtw
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hab : a ≠ b)
    (hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  have hparam_ne : sideParam D p q a ≠ sideParam D p q b := by
    intro hparam
    exact hab (sideParam_injective_onSide_local D hpq ha hb hparam)
  rcases lt_or_gt_of_ne hparam_ne with hlt | hgt
  · exact mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq ha hb hlt
      (fun z hz hbetween =>
        hno z (sbtw_of_sideParam_between_local (D := D) hpq ha hb hz hbetween.1 hbetween.2))
  · have hmem : s(b, a) ∈ sideAtomicEdges D p q :=
      mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq hb ha hgt
        (fun z hz hbetween =>
          hno z ((sbtw_of_sideParam_between_local (D := D) hpq hb ha hz
            hbetween.1 hbetween.2).symm))
    simpa [Sym2.eq_swap] using hmem

lemma segment_subset_of_onSide_local {p q a b : D.vtx}
    (ha : OnSide D p q a) (hb : OnSide D p q b) :
    segment ℝ (D.coord a) (D.coord b) ⊆ segment ℝ (D.coord p) (D.coord q) := by
  exact (convex_segment (D.coord p) (D.coord q)).segment_subset
    (Wbtw.mem_segment ha) (Wbtw.mem_segment hb)

lemma not_sbtw_of_mem_sideAtomicEdges {p q a b z : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  intro hs
  have hmem :
      s(a, b) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
    simpa [sideAtomicEdges] using h
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D h
  have hzseg :
      D.coord z ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide_local D hon.1 hon.2 hs.wbtw.mem_segment
  have hzon : OnSide D p q z := (mem_segment_iff_wbtw (R := ℝ)).mp hzseg
  have hzmem : z ∈ p :: sideInteriorChain D p q ++ [q] :=
    mem_sideChain_of_onSide_local (D := D) hzon
  rcases sideParam_between_of_sbtw_local (D := D) hpq hon.1 hon.2 hzon hs with hbetween | hbetween
  · exact not_sideParam_between_of_mem_sideAtomicEdges D hpq h hzmem hbetween
  · have hswap : s(b, a) ∈ sideAtomicEdges D p q := by
      simpa [Sym2.eq_swap] using h
    exact not_sideParam_between_of_mem_sideAtomicEdges D hpq hswap hzmem hbetween

lemma endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
    {p q a b u v : D.vtx} (hpq : p ≠ q)
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hu : OnSide D p q u) (hv : OnSide D p q v)
    (hmuv : midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord u) (D.coord v)) :
    OnSide D u v a ∧ OnSide D u v b := by
  let ta := sideParam D p q a
  let tb := sideParam D p q b
  let tu := sideParam D p q u
  let tv := sideParam D p q v
  let tm := (ta + tb) / 2
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have ha := hon.1
  have hb := hon.2
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D hpq hside
  have hcoord_ab : D.coord a ≠ D.coord b := by
    intro hcoord
    exact hab (D.coord_inj hcoord)
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
    fun z => not_sbtw_of_mem_sideAtomicEdges D hpq hside
  have hmid_ne_vertex : ∀ z : D.vtx,
      D.coord z ≠ midpoint ℝ (D.coord a) (D.coord b) := by
    intro z hz
    exact hno z (by
      simpa [hz] using sbtw_midpoint_of_ne (R := ℝ) hcoord_ab)
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  have hu_spec := sideParam_spec_of_onSide (D := D) hpq hu
  have hv_spec := sideParam_spec_of_onSide (D := D) hpq hv
  have hm_pq :
      midpoint ℝ (D.coord a) (D.coord b) =
        AffineMap.lineMap (D.coord p) (D.coord q) tm := by
    calc
      midpoint ℝ (D.coord a) (D.coord b)
          = AffineMap.lineMap (D.coord a) (D.coord b) ((1 : ℝ) / 2) := by
              rw [midpoint]
              ext <;> simp [AffineMap.lineMap_apply, invOf_eq_inv] <;> ring
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) ((1 : ℝ) / 2) := by
            rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tm := by
            ext <;> simp [AffineMap.lineMap_apply, tm, ta, tb] <;> ring
  rw [openSegment_eq_image_lineMap] at hmuv
  rcases hmuv with ⟨r, hr, hmuv⟩
  have htm_uv : tm = (1 - r) * tu + r * tv := by
    apply lineMap_param_injective_local (D := D) hpq
    calc
      AffineMap.lineMap (D.coord p) (D.coord q) tm
          = midpoint ℝ (D.coord a) (D.coord b) := hm_pq.symm
      _ = AffineMap.lineMap (D.coord u) (D.coord v) r := hmuv.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) tu)
            (AffineMap.lineMap (D.coord p) (D.coord q) tv) r := by
            rw [hu_spec.2, hv_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * tu + r * tv) := by
            rw [lineMap_lineMap_param]
  have hparam_ne : ta ≠ tb := by
    intro htab
    exact hab (sideParam_injective_onSide_local D hpq ha hb htab)
  have huv_ne : tu ≠ tv := by
    intro htuv
    have huvcoord : D.coord u = D.coord v := by
      calc
        D.coord u = AffineMap.lineMap (D.coord p) (D.coord q) tu := hu_spec.2.symm
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tv := by rw [htuv]
        _ = D.coord v := hv_spec.2
    have hm_eq_u : midpoint ℝ (D.coord a) (D.coord b) = D.coord u := by
      rw [huvcoord] at hmuv
      have hm_eq_v : midpoint ℝ (D.coord a) (D.coord b) = D.coord v := by
        simpa [AffineMap.lineMap_apply] using hmuv.symm
      exact hm_eq_v.trans huvcoord.symm
    exact hmid_ne_vertex u hm_eq_u.symm
  rcases lt_or_gt_of_ne hparam_ne with htab | htba
  · have htm_ab : ta < tm ∧ tm < tb := by
      dsimp [tm]
      constructor <;> nlinarith
    have hnot_u_between : ¬ (ta < tu ∧ tu < tb) := by
      intro hbetween
      exact hno u (sbtw_of_sideParam_between_local
        (D := D) hpq ha hb hu hbetween.1 hbetween.2)
    have hnot_v_between : ¬ (ta < tv ∧ tv < tb) := by
      intro hbetween
      exact hno v (sbtw_of_sideParam_between_local
        (D := D) hpq ha hb hv hbetween.1 hbetween.2)
    rcases lt_or_gt_of_ne huv_ne with htuv | hvtu
    · have htu_tm : tu < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htm_tv : tm < tv := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htu_le_ta : tu ≤ ta := by
        by_contra hle
        exact hnot_u_between ⟨lt_of_not_ge hle, lt_trans htu_tm htm_ab.2⟩
      have htb_le_tv : tb ≤ tv := by
        by_contra hle
        exact hnot_v_between ⟨lt_trans htm_ab.1 htm_tv, lt_of_not_ge hle⟩
      constructor
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv ha htuv
          htu_le_ta (le_trans htab.le htb_le_tv)
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv hb htuv
          (le_trans htu_le_ta htab.le) htb_le_tv
    · have htv_tm : tv < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htm_tu : tm < tu := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htv_le_ta : tv ≤ ta := by
        by_contra hle
        exact hnot_v_between ⟨lt_of_not_ge hle, lt_trans htv_tm htm_ab.2⟩
      have htb_le_tu : tb ≤ tu := by
        by_contra hle
        exact hnot_u_between ⟨lt_trans htm_ab.1 htm_tu, lt_of_not_ge hle⟩
      constructor
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu ha hvtu
          htv_le_ta (le_trans htab.le htb_le_tu)
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu hb hvtu
          (le_trans htv_le_ta htab.le) htb_le_tu
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
  · have htm_ba : tb < tm ∧ tm < ta := by
      dsimp [tm]
      constructor <;> nlinarith
    have hnot_u_between : ¬ (tb < tu ∧ tu < ta) := by
      intro hbetween
      exact hno u ((sbtw_of_sideParam_between_local
        (D := D) hpq hb ha hu hbetween.1 hbetween.2).symm)
    have hnot_v_between : ¬ (tb < tv ∧ tv < ta) := by
      intro hbetween
      exact hno v ((sbtw_of_sideParam_between_local
        (D := D) hpq hb ha hv hbetween.1 hbetween.2).symm)
    rcases lt_or_gt_of_ne huv_ne with htuv | hvtu
    · have htu_tm : tu < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htm_tv : tm < tv := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htu_le_tb : tu ≤ tb := by
        by_contra hle
        exact hnot_u_between ⟨lt_of_not_ge hle, lt_trans htu_tm htm_ba.2⟩
      have hta_le_tv : ta ≤ tv := by
        by_contra hle
        exact hnot_v_between ⟨lt_trans htm_ba.1 htm_tv, lt_of_not_ge hle⟩
      constructor
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv ha htuv
          (le_trans htu_le_tb htba.le) hta_le_tv
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv hb htuv
          htu_le_tb (le_trans htba.le hta_le_tv)
    · have htv_tm : tv < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htm_tu : tm < tu := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htv_le_tb : tv ≤ tb := by
        by_contra hle
        exact hnot_v_between ⟨lt_of_not_ge hle, lt_trans htv_tm htm_ba.2⟩
      have hta_le_tu : ta ≤ tu := by
        by_contra hle
        exact hnot_u_between ⟨lt_trans htm_ba.1 htm_tu, lt_of_not_ge hle⟩
      constructor
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu ha hvtu
          (le_trans htv_le_tb htba.le) hta_le_tu
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu hb hvtu
          htv_le_tb (le_trans htba.le hta_le_tu)
        simpa [OnSide, wbtw_comm (R := ℝ)] using h

lemma mem_triAtomicEdges_iff_local {i : Fin D.n} {e : Sym2 D.vtx} :
    e ∈ triAtomicEdges D i ↔
      e ∈ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.2 (D.tri i).1 := by
  simp [triAtomicEdges, or_assoc]

lemma tri_v₁_ne_v₂_local (i : Fin D.n) : (D.tri i).1 ≠ (D.tri i).2.1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₂_ne_v₃_local (i : Fin D.n) : (D.tri i).2.1 ≠ (D.tri i).2.2 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₃_ne_v₁_local (i : Fin D.n) : (D.tri i).2.2 ≠ (D.tri i).1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]







































lemma tri_vertex₁_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).1 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))

lemma tri_vertex₂_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).2.1 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))

lemma tri_vertex₃_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).2.2 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))





















































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
variable (D : SquareDissection)

lemma solution
    {p q a b : D.vtx} (hpq : p ≠ q)
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hfront : segment ℝ (D.coord p) (D.coord q) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)))
    (support : ∀ u v : D.vtx,
      D.coord u ∈ unitSquareSetLocal → D.coord v ∈ unitSquareSetLocal →
      midpoint ℝ (D.coord a) (D.coord b) ∈
        openSegment ℝ (D.coord u) (D.coord v) →
      OnSide D p q u ∧ OnSide D p q v) :
    IsAtomicEdge D s(a, b) := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have honSquare := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hmSide :
      m ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide_local D honSquare.1 honSquare.2
      (by simpa [m] using midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
  have hmFront : m ∈ frontier unitSquareSetLocal := by
    simpa [unitSquareSetLocal, m] using hfront hmSide
  have hmSq : m ∈ unitSquareSetLocal := by
    have hmf :
        m ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
      simpa [unitSquareSetLocal] using hmFront
    rw [frontier_unitSquare] at hmf
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using
      ⟨⟨hmf.1, hmf.2.2.1⟩, ⟨hmf.2.1, hmf.2.2.2.1⟩⟩
  have hmUnion :
      m ∈ ⋃ i : Fin D.n, convexHull ℝ
        {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2} := by
    have hmSq' : m ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
      simpa [unitSquareSetLocal] using hmSq
    rw [← D.cover] at hmSq'
    exact hmSq'
  rcases Set.mem_iUnion.mp hmUnion with ⟨i, hmi⟩
  have hmiLocal : m ∈ triHullLocal D i := by
    simpa [triHullLocal] using hmi
  have hmTriFront : m ∈ frontier (triHullLocal D i) := by
    exact (mem_frontier_iff_notMem_interior hmiLocal).mpr
      (not_mem_interior_triHull_of_mem_frontier_unitSquare (D := D) hmFront i)
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D hpq hside
  have hcoord_ab : D.coord a ≠ D.coord b := by
    intro hcoord
    exact hab (D.coord_inj hcoord)
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
    fun z => not_sbtw_of_mem_sideAtomicEdges D hpq hside
  have hmid_ne_vertex : ∀ z : D.vtx, D.coord z ≠ m := by
    intro z hz
    exact hno z (by
      simpa [m, hz] using sbtw_midpoint_of_ne (R := ℝ) hcoord_ab)
  rw [triHullLocal, frontier_convexHull_triangle_of_doubleArea_ne_zero
      (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2)
      (D.nondeg i)] at hmTriFront
  rcases hmTriFront with h₁₂₂₃ | h₃₁
  · rcases h₁₂₂₃ with h₁₂ | h₂₃
    · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) :=
        mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).1)
          (hmid_ne_vertex (D.tri i).2.1) h₁₂
      have huv := support (D.tri i).1 (D.tri i).2.1
        (tri_vertex₁_mem_unitSquare D i) (tri_vertex₂_mem_unitSquare D i)
        (by simpa [m] using hmopen)
      have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
        (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
      refine ⟨i, ?_⟩
      rw [mem_triAtomicEdges_iff_local]
      exact Or.inl (mem_sideAtomicEdges_of_onSide_no_sbtw D
        (tri_v₁_ne_v₂_local D i) habuv.1 habuv.2 hab hno)
    · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2) :=
        mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).2.1)
          (hmid_ne_vertex (D.tri i).2.2) h₂₃
      have huv := support (D.tri i).2.1 (D.tri i).2.2
        (tri_vertex₂_mem_unitSquare D i) (tri_vertex₃_mem_unitSquare D i)
        (by simpa [m] using hmopen)
      have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
        (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
      refine ⟨i, ?_⟩
      rw [mem_triAtomicEdges_iff_local]
      exact Or.inr <| Or.inl (mem_sideAtomicEdges_of_onSide_no_sbtw D
        (tri_v₂_ne_v₃_local D i) habuv.1 habuv.2 hab hno)
  · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).2.2) (D.coord (D.tri i).1) :=
      mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).2.2)
        (hmid_ne_vertex (D.tri i).1) h₃₁
    have huv := support (D.tri i).2.2 (D.tri i).1
      (tri_vertex₃_mem_unitSquare D i) (tri_vertex₁_mem_unitSquare D i)
      (by simpa [m] using hmopen)
    have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
      (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
    refine ⟨i, ?_⟩
    rw [mem_triAtomicEdges_iff_local]
    exact Or.inr <| Or.inr (mem_sideAtomicEdges_of_onSide_no_sbtw D
      (tri_v₃_ne_v₁_local D i) habuv.1 habuv.2 hab hno)
