-- Prove2me | solution 1 for Thurston23.hvol_halfBox_eq_ofReal_integral
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T16:29:44.989876+00:00
-- url     : https://prove2.me/submissions/c3252696-243b-409f-bc9f-f7213bd82b98

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_picard

/-!
The volume of the half box as a single integral: Tonelli with the height innermost reduces it
to `∫_D dx dy / (2(1 - x² - y²))` over the base `D = [-½, ½] × [0, ½]`; in polar coordinates the
radial integral is `-¼ log (1 - R²)` with `R = 1/(2 max(|cos θ|, sin θ))`, and the angle folds
twice onto `[0, π/4]`, where the bound is `1/(2 cos θ)`. Verbatim from the mission's source file
`Thurston23.lean`, section `PicardFundamentalDomain` (the vertical, plane, radial and polar integrals).
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section PicardFundamentalDomain

open Set MatrixGroups Quaternion Pointwise


/-! ### Towards the covolume: the vertical integral

The volume of a region lying above a graph reduces to a plane integral, because the
height integral has a closed form. This is the first step of H5, the evaluation of
the box's volume as `G/3`; see `PROBLEMS.md`. -/


/-- `∫_{t ≥ a} t⁻³ dt = 1/(2a²)` for `a > 0`, as a lower Lebesgue integral. -/
theorem lintegral_Ici_inv_cube {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ici a, ENNReal.ofReal ((t ^ (3:ℕ))⁻¹) = ENNReal.ofReal ((2 * a ^ 2)⁻¹) := by
  have hInt : IntegrableOn (fun t : ℝ => (t ^ (3:ℕ))⁻¹) (Set.Ioi a) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) ha).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    have ht0 : (0:ℝ) < t := lt_trans ha ht
    rw [Real.rpow_neg ht0.le]
    norm_num [Real.rpow_natCast]
  have hval : ∫ t in Set.Ioi a, (t ^ (3:ℕ))⁻¹ = (2 * a ^ 2)⁻¹ := by
    have h := integral_Ioi_rpow_of_lt (a := -3) (by norm_num) ha
    rw [show ∫ t in Set.Ioi a, (t ^ (3:ℕ))⁻¹ = ∫ t in Set.Ioi a, t ^ (-3 : ℝ) from
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)]
    · rw [h]
      have ha0 : a ≠ 0 := ne_of_gt ha
      have h2 : a ^ ((-3 : ℝ) + 1) = (a ^ 2)⁻¹ := by
        rw [show ((-3:ℝ) + 1) = -((2:ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le,
          Real.rpow_natCast]
      rw [h2]
      field_simp
      try ring
    · have ht0 : (0:ℝ) < t := lt_trans ha ht
      rw [Real.rpow_neg ht0.le]
      norm_num [Real.rpow_natCast]
  have hIci : ∫⁻ t in Set.Ici a, ENNReal.ofReal ((t ^ (3:ℕ))⁻¹)
      = ∫⁻ t in Set.Ioi a, ENNReal.ofReal ((t ^ (3:ℕ))⁻¹) := by
    rw [← Set.Ioi_union_left, lintegral_union (measurableSet_singleton a)]
    · simp
    · exact Set.disjoint_singleton_right.2 (by simp)
  rw [hIci, ← ofReal_integral_eq_lintegral_ofReal hInt]
  · rw [hval]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := lt_trans ha ht
    positivity


/-- `ℝ³ ≃ ℝ × ℝ²`, splitting off the height. -/
noncomputable def splitEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

theorem measurePreserving_splitEquiv :
    MeasurePreserving splitEquiv (volume : Measure (Fin 3 → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have h2 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    (MeasurePreserving.id _).prod (volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

theorem splitEquiv_apply (x : Fin 3 → ℝ) : splitEquiv x = (x 2, (x 0, x 1)) := rfl

/-- **H5, step 1.** The hyperbolic volume of `{(x, y, t) : (x, y) ∈ D, g (x, y) ≤ t}`
is `∫_D dx dy / (2 g(x,y)²)`: the height integral has the closed form
`∫_{t ≥ a} t⁻³ dt = 1/(2a²)`, and the rest is Tonelli. -/
theorem hvol_above_graph {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) {g : ℝ × ℝ → ℝ}
    (hgm : Measurable g) (hgpos : ∀ z ∈ D, 0 < g z) :
    hvol {p : H3 | ((p.1 0, p.1 1) ∈ D) ∧ g (p.1 0, p.1 1) ≤ p.1 2}
      = ∫⁻ z in D, ENNReal.ofReal ((2 * g z ^ 2)⁻¹) := by
  classical
  set A : Set (Fin 3 → ℝ) := {x | ((x 0, x 1) ∈ D) ∧ g (x 0, x 1) ≤ x 2} with hA
  set B : Set (ℝ × (ℝ × ℝ)) := {y | y.2 ∈ D ∧ g y.2 ≤ y.1} with hB
  set σ : ℝ × (ℝ × ℝ) → ENNReal := fun y => ENNReal.ofReal ((y.1 ^ (3:ℕ))⁻¹) with hσ
  have hc0 : Measurable fun x : Fin 3 → ℝ => (x 0, x 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hAm : MeasurableSet A :=
    (hc0 hD).inter (measurableSet_le (hgm.comp hc0) (measurable_pi_apply 2))
  have hBm : MeasurableSet B :=
    ((measurable_snd hD)).inter (measurableSet_le (hgm.comp measurable_snd) measurable_fst)
  have hσm : Measurable σ := (measurable_fst.pow_const 3).inv.ennreal_ofReal
  -- the region sits over the half-space, so preimage and image match up
  have hAsub : A ⊆ Set.range (Subtype.val : H3 → Fin 3 → ℝ) := by
    rintro x ⟨hxD, hxg⟩
    exact ⟨⟨x, lt_of_lt_of_le (hgpos _ hxD) hxg⟩, rfl⟩
  have himg : Subtype.val '' (Subtype.val ⁻¹' A : Set H3) = A := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.2 hAsub]
  -- transport to `ℝ³`
  have step1 : hvol {p : H3 | ((p.1 0, p.1 1) ∈ D) ∧ g (p.1 0, p.1 1) ≤ p.1 2}
      = ∫⁻ x in A, ρ x := by
    rw [show {p : H3 | ((p.1 0, p.1 1) ∈ D) ∧ g (p.1 0, p.1 1) ≤ p.1 2}
        = Subtype.val ⁻¹' A from rfl, hvol_apply (measurable_subtype_coe hAm), himg]
  -- the integrand transported along the splitting
  have hpt : ∀ x : Fin 3 → ℝ, A.indicator ρ x = B.indicator σ (splitEquiv x) := by
    intro x
    rw [splitEquiv_apply]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by exact hx)]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by exact hx)]
  -- Tonelli, with the height innermost
  have step2 : ∫⁻ x in A, ρ x = ∫⁻ z : ℝ × ℝ, ∫⁻ t : ℝ, B.indicator σ (t, z) := by
    rw [← lintegral_indicator hAm]
    calc ∫⁻ x, A.indicator ρ x
        = ∫⁻ x, B.indicator σ (splitEquiv x) := lintegral_congr hpt
      _ = ∫⁻ y, B.indicator σ y ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
          measurePreserving_splitEquiv.lintegral_comp (hσm.indicator hBm)
      _ = ∫⁻ z : ℝ × ℝ, ∫⁻ t : ℝ, B.indicator σ (t, z) :=
          lintegral_prod_symm _ (hσm.indicator hBm).aemeasurable
  -- the inner integral, by the closed form of the height integral
  have step3 : ∀ z : ℝ × ℝ, (∫⁻ t : ℝ, B.indicator σ (t, z))
      = D.indicator (fun z => ENNReal.ofReal ((2 * g z ^ 2)⁻¹)) z := by
    intro z
    by_cases hz : z ∈ D
    · rw [Set.indicator_of_mem hz]
      have hfun : ∀ t : ℝ, B.indicator σ (t, z)
          = (Set.Ici (g z)).indicator (fun t => ENNReal.ofReal ((t ^ (3:ℕ))⁻¹)) t := by
        intro t
        by_cases ht : g z ≤ t
        · rw [Set.indicator_of_mem (show (t, z) ∈ B from ⟨hz, ht⟩),
            Set.indicator_of_mem (show t ∈ Set.Ici (g z) from ht)]
        · rw [Set.indicator_of_notMem (fun h => ht h.2),
            Set.indicator_of_notMem (show t ∉ Set.Ici (g z) from ht)]
      simp_rw [hfun]
      rw [lintegral_indicator measurableSet_Ici]
      exact lintegral_Ici_inv_cube (hgpos z hz)
    · rw [Set.indicator_of_notMem hz]
      have hfun : ∀ t : ℝ, B.indicator σ (t, z) = 0 := by
        intro t
        exact Set.indicator_of_notMem (fun h => hz h.1) _
      simp_rw [hfun]
      simp
  rw [step1, step2]
  simp_rw [step3]
  rw [lintegral_indicator hD]

/-- The plane region under the half box: `|x| ≤ ½`, `0 ≤ y ≤ ½`. -/
def boxBase : Set (ℝ × ℝ) := Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Icc (0:ℝ) (1/2)

theorem measurableSet_boxBase : MeasurableSet boxBase :=
  measurableSet_Icc.prod measurableSet_Icc

/-- On the base, `1 - x² - y² ≥ ½`. -/
theorem boxBase_pos {z : ℝ × ℝ} (hz : z ∈ boxBase) : 1 / 2 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  nlinarith [h1, h2, h3, h4]

/-- The half box is the region above the graph of `√(1 - x² - y²)` over the base. -/
theorem halfBox_eq_above_graph :
    halfBox = {p : H3 | ((p.1 0, p.1 1) ∈ boxBase) ∧
      Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2) ≤ p.1 2} := by
  ext p
  have ht : 0 < p.1 2 := p.2
  constructor
  · rintro ⟨hx, hy0, hy1, hN⟩
    have hxmem : (p.1 0, p.1 1) ∈ boxBase := by
      obtain ⟨hx1, hx2⟩ := abs_le.1 hx
      exact ⟨⟨by linarith, by linarith⟩, ⟨hy0, hy1⟩⟩
    refine ⟨hxmem, ?_⟩
    have hNval : N p.1 = p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      rw [hNval] at hN
      nlinarith [hN]
    calc Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2)
        ≤ Real.sqrt ((p.1 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = p.1 2 := Real.sqrt_sq ht.le
  · rintro ⟨hz, hge⟩
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    have hpos : 0 ≤ 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 := by
      have := boxBase_pos (z := (p.1 0, p.1 1)) ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      simp only at this
      linarith
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      have h := Real.sq_sqrt hpos
      nlinarith [hge, Real.sqrt_nonneg (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2), h]
    have hNval : N p.1 = p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, h3, h4, ?_⟩
    rw [hNval]
    nlinarith [hsq]

/-- **The volume of the half box as a plane integral.** This is what the polar
decomposition and the log-sine values are meant to evaluate: the answer should be
`G/3`, `G` Catalan's constant. -/
theorem hvol_halfBox_eq_plane_integral :
    hvol halfBox = ∫⁻ z in boxBase, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) := by
  have hgm : Measurable fun z : ℝ × ℝ => Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    fun_prop
  have hgpos : ∀ z ∈ boxBase, 0 < Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    intro z hz
    have := boxBase_pos hz
    exact Real.sqrt_pos.2 (by linarith)
  rw [halfBox_eq_above_graph, hvol_above_graph measurableSet_boxBase hgm hgpos]
  refine setLIntegral_congr_fun measurableSet_boxBase fun z hz => ?_
  have hpos : 0 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
    have := boxBase_pos hz
    linarith
  rw [Real.sq_sqrt hpos]

/-! ### Towards the covolume: the radial integral

In polar coordinates the plane integral above has inner integral
`∫₀^R r dr / (2(1 - r²)) = -¼ log (1 - R²)`, which is where the logarithm that
becomes a log-sine integral first appears. -/


theorem integral_radial {R : ℝ} (h0 : 0 ≤ R) (h1 : R < 1) :
    ∫ r in (0:ℝ)..R, r / (2 * (1 - r ^ 2)) = -(1/4) * Real.log (1 - R ^ 2) := by
  have hpos : ∀ r ∈ Set.uIcc (0:ℝ) R, 0 < 1 - r ^ 2 := by
    intro r hr
    rw [Set.uIcc_of_le h0] at hr
    obtain ⟨hr0, hr1⟩ := hr
    nlinarith [hr0, hr1, h1]
  have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) R,
      HasDerivAt (fun r : ℝ => -(1/4) * Real.log (1 - r ^ 2)) (r / (2 * (1 - r ^ 2))) r := by
    intro r hr
    have hne : (1 - r ^ 2) ≠ 0 := ne_of_gt (hpos r hr)
    have h1' : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      simpa using ((hasDerivAt_pow 2 r).const_sub 1)
    have h2 : HasDerivAt (fun r : ℝ => Real.log (1 - r ^ 2)) (-(2 * r) / (1 - r ^ 2)) r :=
      h1'.log hne
    have h3 := h2.const_mul (-(1/4) : ℝ)
    convert h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Set.uIcc 0 R) := by
    refine ContinuousOn.div continuousOn_id (by fun_prop) fun r hr => ?_
    have := hpos r hr
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

section Polar

open scoped Real

/-! ### The base in polar coordinates -/

/-- The radial extent of the base `boxBase` in the direction `θ`: the ray leaves the
base where `|x| = ½` or `y = ½`, whichever comes first, at `r = 1/(2 max(|cos θ|, sin θ))`. -/
noncomputable def radialBound (θ : ℝ) : ℝ := 1 / (2 * max |Real.cos θ| (Real.sin θ))

theorem half_lt_max_abs_cos_sin {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    1 / 2 < max |Real.cos θ| (Real.sin θ) := by
  by_contra h
  push_neg at h
  have h1 : |Real.cos θ| ≤ 1 / 2 := le_trans (le_max_left _ _) h
  have h2 : Real.sin θ ≤ 1 / 2 := le_trans (le_max_right _ _) h
  have h3 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have h4 : |Real.cos θ| * |Real.cos θ| ≤ 1 / 2 * (1 / 2) :=
    mul_le_mul h1 h1 (abs_nonneg _) (by norm_num)
  have h5 : Real.cos θ ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    nlinarith [h4]
  have h6 := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem radialBound_pos {θ : ℝ} (hθ : θ ∈ Icc 0 π) : 0 < radialBound θ := by
  unfold radialBound
  have := half_lt_max_abs_cos_sin hθ
  positivity

theorem radialBound_lt_one {θ : ℝ} (hθ : θ ∈ Icc 0 π) : radialBound θ < 1 := by
  unfold radialBound
  have := half_lt_max_abs_cos_sin hθ
  rw [div_lt_one (by linarith)]
  linarith

/-- A point of the polar target lands in the base iff its angle is in `[0, π)` and its
radius is at most `radialBound`. -/
theorem polarCoord_symm_mem_boxBase_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ boxBase ↔ p.2 ∈ Ico 0 π ∧ p.1 ≤ radialBound p.2 := by
  obtain ⟨r, θ⟩ := p
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [ht] at hp
  simp only [mem_prod, mem_Ioi, mem_Ioo] at hp
  obtain ⟨hr, hθ1, hθ2⟩ := hp
  have hsymm : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
  rw [hsymm]
  simp only [boxBase, mem_prod, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    have hsin : 0 ≤ Real.sin θ := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hr (neg_pos.2 h)]
    have hθ0 : 0 ≤ θ := by
      by_contra h
      push_neg at h
      exact absurd hsin (not_le.2 (Real.sin_neg_of_neg_of_neg_pi_lt h hθ1))
    refine ⟨⟨hθ0, hθ2⟩, ?_⟩
    have hM := half_lt_max_abs_cos_sin ⟨hθ0, hθ2.le⟩
    unfold radialBound
    rw [le_div_iff₀ (by linarith)]
    have habs : r * |Real.cos θ| ≤ 1 / 2 := by
      have : |r * Real.cos θ| ≤ 1 / 2 := abs_le.2 ⟨by linarith, hx2⟩
      rwa [abs_mul, abs_of_pos hr] at this
    rcases le_total |Real.cos θ| (Real.sin θ) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · rintro ⟨⟨hθ0, _⟩, hR⟩
    have hM := half_lt_max_abs_cos_sin ⟨hθ0, hθ2.le⟩
    unfold radialBound at hR
    rw [le_div_iff₀ (by linarith)] at hR
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ2.le
    have h1 : r * |Real.cos θ| ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_left |Real.cos θ| (Real.sin θ)) hr.le
      linarith
    have h2 : r * Real.sin θ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_right |Real.cos θ| (Real.sin θ)) hr.le
      linarith
    have h3 : |r * Real.cos θ| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hr]; exact h1
    obtain ⟨h4, h5⟩ := abs_le.1 h3
    exact ⟨⟨h4, h5⟩, ⟨mul_nonneg hr.le hsin, h2⟩⟩

/-- **The plane integral in polar coordinates**, as an iterated integral: angle outside,
radius inside. -/
theorem lintegral_boxBase_polar :
    ∫⁻ z in boxBase, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹)
      = ∫⁻ θ in Ico 0 π, ∫⁻ r in Ioc 0 (radialBound θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
  set F : ℝ × ℝ → ENNReal := fun z => ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) with hF
  set G : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.1 / (2 * (1 - p.1 ^ 2))) with hG
  set S : Set (ℝ × ℝ) := {p | p.2 ∈ Ico 0 π ∧ 0 < p.1 ∧ p.1 ≤ radialBound p.2} with hS
  have hGm : Measurable G := by fun_prop
  have hRm : Measurable radialBound := by
    unfold radialBound
    fun_prop
  have hSm : MeasurableSet S := by
    refine (measurableSet_Ico.preimage measurable_snd).inter ?_
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hRm.comp measurable_snd))
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  -- the integrand on the polar side, pointwise
  have hpt : ∀ p : ℝ × ℝ, polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • boxBase.indicator F (polarCoord.symm p)) p
      = S.indicator G p := by
    intro p
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      have hr : 0 < p.1 := by
        rw [ht] at hp
        exact hp.1
      by_cases hpS : p ∈ S
      · rw [indicator_of_mem hpS]
        have hmem : polarCoord.symm p ∈ boxBase :=
          (polarCoord_symm_mem_boxBase_iff hp).2 ⟨hpS.1, hpS.2.2⟩
        rw [indicator_of_mem hmem]
        have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
        simp only [hF, hG, smul_eq_mul, hsymm]
        rw [← ENNReal.ofReal_mul hr.le]
        congr 1
        have key : 1 - (p.1 * Real.cos p.2) ^ 2 - (p.1 * Real.sin p.2) ^ 2 = 1 - p.1 ^ 2 := by
          have := Real.sin_sq_add_cos_sq p.2
          linear_combination (-(p.1 ^ 2)) * this
        rw [key, div_eq_mul_inv]
      · rw [indicator_of_notMem hpS]
        have hnot : polarCoord.symm p ∉ boxBase := fun h =>
          hpS ⟨((polarCoord_symm_mem_boxBase_iff hp).1 h).1, hr,
            ((polarCoord_symm_mem_boxBase_iff hp).1 h).2⟩
        rw [indicator_of_notMem hnot, smul_zero]
    · rw [indicator_of_notMem hp]
      have hpS : p ∉ S := by
        intro h
        apply hp
        rw [ht]
        exact ⟨h.2.1, ⟨by linarith [h.1.1, Real.pi_pos], h.1.2⟩⟩
      rw [indicator_of_notMem hpS]
  calc ∫⁻ z in boxBase, F z
      = ∫⁻ z, boxBase.indicator F z := (lintegral_indicator measurableSet_boxBase F).symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • boxBase.indicator F (polarCoord.symm p) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p, S.indicator G p := by
        rw [← lintegral_indicator polarCoord.open_target.measurableSet]
        exact lintegral_congr hpt
    _ = ∫⁻ θ, ∫⁻ r, S.indicator G (r, θ) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_symm _ (hGm.indicator hSm).aemeasurable
    _ = ∫⁻ θ in Ico 0 π, ∫⁻ r in Ioc 0 (radialBound θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
        rw [← lintegral_indicator measurableSet_Ico]
        refine lintegral_congr fun θ => ?_
        by_cases hθ : θ ∈ Ico 0 π
        · rw [indicator_of_mem hθ, ← lintegral_indicator measurableSet_Ioc]
          refine lintegral_congr fun r => ?_
          by_cases hr : r ∈ Ioc 0 (radialBound θ)
          · rw [indicator_of_mem hr, indicator_of_mem (show (r, θ) ∈ S from ⟨hθ, hr.1, hr.2⟩)]
          · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr ⟨h.2.1, h.2.2⟩)]
        · rw [indicator_of_notMem hθ]
          have h0 : ∀ r, S.indicator G (r, θ) = 0 := fun r =>
            indicator_of_notMem (fun h => hθ h.1) _
          simp_rw [h0]
          simp

/-- The inner (radial) integral, evaluated. -/
theorem lintegral_radial {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    ∫⁻ r in Ioc 0 (radialBound θ), ENNReal.ofReal (r / (2 * (1 - r ^ 2)))
      = ENNReal.ofReal (-(1/4) * Real.log (1 - radialBound θ ^ 2)) := by
  have hR0 := radialBound_pos hθ
  have hR1 := radialBound_lt_one hθ
  have hpos : ∀ r ∈ Icc (0:ℝ) (radialBound θ), 0 < 1 - r ^ 2 := by
    intro r hr
    nlinarith [hr.1, hr.2]
  have hcont : ContinuousOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Icc 0 (radialBound θ)) := by
    refine ContinuousOn.div continuousOn_id (by fun_prop) fun r hr => ?_
    have := hpos r hr
    positivity
  have hint : IntegrableOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Ioc 0 (radialBound θ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1
      (ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hR0.le]))
  rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hR0.le,
    integral_radial hR0.le hR1]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  have := hpos r ⟨hr.1.le, hr.2⟩
  exact div_nonneg hr.1.le (by linarith)

theorem continuousOn_radialBound : ContinuousOn radialBound (Icc 0 π) := by
  unfold radialBound
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun θ hθ => ?_
  have := half_lt_max_abs_cos_sin hθ
  exact ne_of_gt (by linarith)

theorem continuousOn_g :
    ContinuousOn (fun θ => -(1/4) * Real.log (1 - radialBound θ ^ 2)) (Icc 0 π) := by
  refine continuousOn_const.mul (ContinuousOn.log ?_ fun θ hθ => ?_)
  · exact continuousOn_const.sub (continuousOn_radialBound.pow 2)
  · have h1 := radialBound_pos hθ
    have h2 := radialBound_lt_one hθ
    exact ne_of_gt (by nlinarith)

/-- The outer (angular) integral as a real integral. -/
theorem lintegral_Ico_g :
    ∫⁻ θ in Ico 0 π, ENNReal.ofReal (-(1/4) * Real.log (1 - radialBound θ ^ 2))
      = ENNReal.ofReal (∫ θ in (0:ℝ)..π, -(1/4) * Real.log (1 - radialBound θ ^ 2)) := by
  have hint : IntegrableOn (fun θ => -(1/4) * Real.log (1 - radialBound θ ^ 2)) (Ioc 0 π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).1
      (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le Real.pi_pos.le]; exact continuousOn_g))
  rw [restrict_Ico_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have h1 := radialBound_pos ⟨hθ.1.le, hθ.2⟩
  have h2 := radialBound_lt_one ⟨hθ.1.le, hθ.2⟩
  have hlog : Real.log (1 - radialBound θ ^ 2) ≤ 0 :=
    Real.log_nonpos (by nlinarith) (by nlinarith)
  show (0:ℝ) ≤ -(1/4) * Real.log (1 - radialBound θ ^ 2)
  linarith

/-! ### Folding the angle onto `[0, π/4]` -/

theorem radialBound_pi_sub (θ : ℝ) : radialBound (π - θ) = radialBound θ := by
  simp only [radialBound, Real.cos_pi_sub, Real.sin_pi_sub, abs_neg]

theorem cos_nonneg_of_mem_pi_div_four {θ : ℝ} (hθ : θ ∈ Icc 0 (π/4)) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

theorem sin_le_cos_of_mem_pi_div_four {θ : ℝ} (hθ : θ ∈ Icc 0 (π/4)) :
    Real.sin θ ≤ Real.cos θ := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.1]) (by linarith [hθ.2])

/-- On `[0, π/4]` the ray leaves the base through `x = ½`. -/
theorem radialBound_of_mem {θ : ℝ} (hθ : θ ∈ Icc 0 (π/4)) :
    radialBound θ = 1 / (2 * Real.cos θ) := by
  rw [radialBound, abs_of_nonneg (cos_nonneg_of_mem_pi_div_four hθ),
    max_eq_left (sin_le_cos_of_mem_pi_div_four hθ)]

theorem radialBound_pi_div_two_sub {θ : ℝ} (hθ : θ ∈ Icc 0 (π/4)) :
    radialBound (π/2 - θ) = radialBound θ := by
  rw [radialBound_of_mem hθ, radialBound, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  rw [abs_of_nonneg hsin0, max_eq_right (sin_le_cos_of_mem_pi_div_four hθ)]

/-- The angular integral over `[0, π]` folds twice onto `[0, π/4]`, where the radial
bound is `1/(2 cos θ)`. -/
theorem integral_g_fold :
    ∫ θ in (0:ℝ)..π, -(1/4) * Real.log (1 - radialBound θ ^ 2)
      = -∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) := by
  set g : ℝ → ℝ := fun θ => -(1/4) * Real.log (1 - radialBound θ ^ 2) with hg
  have hcont : ContinuousOn g (Icc 0 π) := continuousOn_g
  have hI : ∀ a b, 0 ≤ a → a ≤ b → b ≤ π → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    exact ContinuousOn.intervalIntegrable
      (hcont.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
  have hpi := Real.pi_pos
  have h1 : ∫ θ in (0:ℝ)..π, g θ = (∫ θ in (0:ℝ)..π/2, g θ) + ∫ θ in (π/2)..π, g θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI 0 (π/2) le_rfl (by linarith) (by linarith))
      (hI (π/2) π (by linarith) (by linarith) le_rfl)).symm
  have h2 : ∫ θ in (π/2)..π, g θ = ∫ θ in (0:ℝ)..π/2, g θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/2) (f := g) π
    rw [sub_zero, show π - π/2 = π/2 by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hg, radialBound_pi_sub]
  have h3 : ∫ θ in (0:ℝ)..π/2, g θ = (∫ θ in (0:ℝ)..π/4, g θ) + ∫ θ in (π/4)..π/2, g θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI 0 (π/4) le_rfl (by linarith) (by linarith))
      (hI (π/4) (π/2) (by linarith) (by linarith) (by linarith))).symm
  have h4 : ∫ θ in (π/4)..π/2, g θ = ∫ θ in (0:ℝ)..π/4, g θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/4) (f := g) (π/2)
    rw [sub_zero, show π/2 - π/4 = π/4 by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hg, radialBound_pi_div_two_sub hθ]
  have h5 : ∫ θ in (0:ℝ)..π/4, g θ
      = ∫ θ in (0:ℝ)..π/4, -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    have hsq : (1 / (2 * Real.cos θ)) ^ 2 = 1 / (4 * Real.cos θ ^ 2) := by
      rw [div_pow, mul_pow]; norm_num
    simp only [hg, radialBound_of_mem hθ, hsq]
  have h6 : ∫ θ in (0:ℝ)..π/4, -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -(1/4) * ∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) :=
    intervalIntegral.integral_const_mul _ _
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- **H5, step 2.** The plane integral giving the volume of the half box is minus
`∫₀^{π/4} log (1 - sec²θ/4) dθ`. -/
theorem lintegral_boxBase_eq :
    ∫⁻ z in boxBase, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹)
      = ENNReal.ofReal (-∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  rw [lintegral_boxBase_polar, ← integral_g_fold, ← lintegral_Ico_g]
  refine setLIntegral_congr_fun measurableSet_Ico fun θ hθ => ?_
  exact lintegral_radial ⟨hθ.1, hθ.2.le⟩

/-- **The volume of the half box as a single integral**:
`hvol halfBox = -∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ`. Steps 1 and 2 of H5 together. -/
theorem hvol_halfBox_eq_ofReal_integral :
    hvol halfBox
      = ENNReal.ofReal (-∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  rw [hvol_halfBox_eq_plane_integral, lintegral_boxBase_eq]

end Polar

end PicardFundamentalDomain

end Thurston23

open MeasureTheory in
theorem solution :
    Thurston23.hvol Thurston23.halfBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) :=
  Thurston23.hvol_halfBox_eq_ofReal_integral
