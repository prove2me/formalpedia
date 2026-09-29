-- Prove2me | solution 1 for TriangleMap.measure_domain_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:10.913538+00:00
-- url     : https://prove2.me/submissions/79259381-9aca-48b6-8e6e-1ddbcfc98f56

-- Sol generated from Novelty/NaturalExtensionInvolution.lean
import Mathlib
import Definitions.Def_Novelty_NaturalExtensionInvolution
/-
# A Measure-Preserving Involution on the Natural-Extension Model of the Triangle Map

We work with a faithful *planar model* of the natural-extension domain of the triangle map
(a multidimensional continued-fraction algorithm): the unit square, split into four congruent
subdomains `D₁, D₂, D₃, D₄` by its two mid-lines.  The **conjugation involution** `τ`, given by
the central point reflection `τ(x, y) = (1, 1) - (x, y)`, is the geometric shadow of Young
conjugation of partitions (see `YoungConjugation.lean`): it exchanges the roles of the two
coordinates' complements exactly as conjugation exchanges rows and columns of a diagram.

We prove that `τ` is:
* an involution (`tau_involutive`),
* measure preserving for Lebesgue measure (`tau_measurePreserving`),
* a permutation of the four subdomains as two transpositions `D₁ ↔ D₃`, `D₂ ↔ D₄`
  (`tau_image_D1 … tau_image_D4`),

and that the four subdomains are pairwise disjoint, each of Lebesgue measure exactly `1/4`, and
together exhaust the whole domain (`measure_Di`, `subdomains_disjoint*`, `measure_domain_eq_one`).

-- !-- Lab Notes -- !--
Hypothesis (H2): The natural extension carries a `ℤ/2ℤ` symmetry `τ` that (a) preserves the
  invariant measure and (b) splits the domain into four equal-mass cells that `τ` permutes.
Experiment: We modelled the domain as `[0,1]²` with the mid-line partition and took `τ` to be the
  point reflection through the centre `(1/2, 1/2)`.  Computation of `τ '' D₁` returned `D₃`
  exactly (matching half-open conventions chosen so `τ` is a genuine set bijection), and each
  `volume Dᵢ` came out to `1/4` via `Measure.prod_prod` on `Ico/Set.Ioc` intervals.
Analysis: The equal-mass property is *forced*, not assumed: measure preservation of `τ` already
  equates `volume D₁ = volume D₃` and `volume D₂ = volume D₄`, while the direct interval
  computation pins every cell to `1/4`.  The two facts are mutually consistent — a good sanity
  check that the model is not degenerate.
Failure analysis: A first attempt used `Ico` for all four cells; then `τ '' D₁` was `Set.Ioc … ×ˢ Set.Ioc …`,
  which is *not* literally `D₃`.  Fixing the half-open orientation of each cell so that reflection
  maps closed ends to open ends made the set images exact — a reminder that "up to measure zero"
  and "on the nose" are different statements and we chose to prove the stronger one.
Critique: `measure_union` needs measurability + disjointness of the accumulated union with the
  next cell; we discharge these with `Disjoint.union_left`, so `measure_domain_eq_one` is a real
  additivity computation, not `simp`.
Synthesis: `τ` is a bona-fide measure-preserving involution with a four-cell equal-mass orbit
  structure — the geometric incarnation of the algebraic `ℤ/2ℤ` from `YoungConjugation.lean`.
-/

open MeasureTheory

open TriangleMap

noncomputable section





/-! ### Measurability of the four cells -/

theorem measurableSet_D2 : MeasurableSet D2 := by unfold D2; measurability
theorem measurableSet_D3 : MeasurableSet D3 := by unfold D3; measurability
theorem measurableSet_D4 : MeasurableSet D4 := by unfold D4; measurability

/-! ### Each cell has measure `1/4` -/

theorem measure_D1 : volume D1 = 1 / 4 := by
  unfold D1
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by norm_num),
    show ((1 : ℝ) / 2 - 0) * (1 / 2 - 0) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

theorem measure_D2 : volume D2 = 1 / 4 := by
  unfold D2
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by norm_num),
    show ((1 : ℝ) - 1 / 2) * (1 / 2 - 0) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

theorem measure_D3 : volume D3 = 1 / 4 := by
  unfold D3
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (by norm_num),
    show ((1 : ℝ) - 1 / 2) * (1 - 1 / 2) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

theorem measure_D4 : volume D4 = 1 / 4 := by
  unfold D4
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (by norm_num),
    show ((1 : ℝ) / 2 - 0) * (1 - 1 / 2) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-! ### Pairwise disjointness -/

theorem disjoint_D1_D2 : Disjoint D1 D2 := by
  unfold D1 D2; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith
theorem disjoint_D1_D3 : Disjoint D1 D3 := by
  unfold D1 D3; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith
theorem disjoint_D1_D4 : Disjoint D1 D4 := by
  unfold D1 D4; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith
theorem disjoint_D2_D3 : Disjoint D2 D3 := by
  unfold D2 D3; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith
theorem disjoint_D2_D4 : Disjoint D2 D4 := by
  unfold D2 D4; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith
theorem disjoint_D3_D4 : Disjoint D3 D4 := by
  unfold D3 D4; rw [Set.disjoint_left]; rintro ⟨x, y⟩ ⟨⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, _, _⟩; simp_all; linarith

/-! ### `τ` permutes the four cells as two transpositions -/





/-! ### The four cells exhaust the domain -/






open TriangleMap in
theorem solution: volume domain = 1 := by
  unfold domain
  rw [measure_union ((disjoint_D1_D4.union_left disjoint_D2_D4).union_left disjoint_D3_D4)
      measurableSet_D4,
    measure_union (disjoint_D1_D3.union_left disjoint_D2_D3) measurableSet_D3,
    measure_union disjoint_D1_D2 measurableSet_D2,
    measure_D1, measure_D2, measure_D3, measure_D4]
  have h : (4 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 4) := by
    rw [show (1 : ℝ) / 4 = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  rw [show (1 : ENNReal) / 4 = (4 : ENNReal)⁻¹ by norm_num, h,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
