-- Prove2me | solution 1 for Thurston23.hvol_eisBox_eq_ofReal_integral
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-14T16:24:22.58251+00:00
-- url     : https://prove2.me/submissions/1a270956-c534-42ca-b714-35c977a5c53a

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_eisenstein

/-!
The volume of the box over the rhombus as a single integral. Verbatim from the mission's source
files: the vertical and radial integrals of `Thurston23.lean`, and the section `EisVolume` of
`Thurston23Eisenstein.lean`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section ReusedA

open Set MatrixGroups Quaternion Pointwise

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

end ReusedA

section EisBase

open Complex

theorem eisBase_of_open {w : ℂ} (h : eisBaseOpen w) : eisBase w :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/-- On the rhombus `|w|² ≤ ⅓`. -/
theorem normSq_le_of_eisBase {w : ℂ} (hw : eisBase w) : normSq w ≤ 1 / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have hsq : (Real.sqrt 3 * w.im) ^ 2 = 3 * w.im ^ 2 := by rw [mul_pow, sqrt3_sq]
  rw [Complex.normSq_apply]
  nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 / 2 - w.re),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (w.re + Real.sqrt 3 * w.im))
      (by linarith : (0:ℝ) ≤ 1 + (w.re + Real.sqrt 3 * w.im) - 2 * w.re)]

end EisBase

section EisVolume

open Set MatrixGroups Quaternion Pointwise
open scoped Real

/-- The rhombus as a subset of `ℝ²`. -/
def eisBaseSet : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 / 2 ∧ 0 ≤ z.1 + Real.sqrt 3 * z.2 ∧ z.1 + Real.sqrt 3 * z.2 ≤ 1}

theorem measurableSet_eisBaseSet : MeasurableSet eisBaseSet := by
  have hv : Measurable fun z : ℝ × ℝ => z.1 + Real.sqrt 3 * z.2 :=
    measurable_fst.add (measurable_snd.const_mul _)
  have hset : eisBaseSet = {z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ 1 / 2} ∩
      {z : ℝ × ℝ | 0 ≤ z.1 + Real.sqrt 3 * z.2} ∩ {z : ℝ × ℝ | z.1 + Real.sqrt 3 * z.2 ≤ 1} := by
    ext z
    simp only [eisBaseSet, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact (((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (measurableSet_le measurable_const hv)).inter (measurableSet_le hv measurable_const)

theorem eisBaseSet_pos {z : ℝ × ℝ} (hz : z ∈ eisBaseSet) : 2 / 3 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
  have h := normSq_le_of_eisBase (w := ⟨z.1, z.2⟩) hz
  rw [Complex.normSq_mk] at h
  nlinarith

theorem eisBox_eq_above_graph :
    eisBox = {p : H3 | ((p.1 0, p.1 1) ∈ eisBaseSet) ∧
      Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2) ≤ p.1 2} := by
  ext p
  have ht : 0 < p.1 2 := p.2
  have hNval : N p.1 = p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
  constructor
  · rintro ⟨hb, hN⟩
    refine ⟨hb, ?_⟩
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      rw [hNval] at hN
      nlinarith [hN]
    calc Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2)
        ≤ Real.sqrt ((p.1 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = p.1 2 := Real.sqrt_sq ht.le
  · rintro ⟨hz, hge⟩
    have hpos := eisBaseSet_pos hz
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      have h := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2)
      nlinarith [hge, Real.sqrt_nonneg (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2), h]
    refine ⟨hz, ?_⟩
    rw [hNval]
    nlinarith [hsq]

theorem hvol_eisBox_eq_plane_integral :
    hvol eisBox = ∫⁻ z in eisBaseSet, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) := by
  have hgm : Measurable fun z : ℝ × ℝ => Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    fun_prop
  have hgpos : ∀ z ∈ eisBaseSet, 0 < Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    intro z hz
    have := eisBaseSet_pos hz
    exact Real.sqrt_pos.2 (by linarith)
  rw [eisBox_eq_above_graph, hvol_above_graph measurableSet_eisBaseSet hgm hgpos]
  refine setLIntegral_congr_fun measurableSet_eisBaseSet fun z hz => ?_
  have hpos : 0 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
    have := eisBaseSet_pos hz
    linarith
  rw [Real.sq_sqrt hpos]

theorem cos_sub_pi_div_three' (θ : ℝ) :
    Real.cos (θ - π / 3) = Real.cos θ / 2 + Real.sqrt 3 / 2 * Real.sin θ := by
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

/-- The radial extent of the rhombus in the direction `θ`. -/
noncomputable def eisRadial (θ : ℝ) : ℝ :=
  1 / (2 * max (Real.cos θ) (Real.cos (θ - π / 3)))

theorem half_lt_max_cos {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    1 / 2 < max (Real.cos θ) (Real.cos (θ - π / 3)) := by
  have hpi := Real.pi_pos
  rcases le_or_gt θ (π / 6) with h | h
  · have habs : |θ| < π / 3 := abs_lt.2 ⟨by linarith [hθ.1], by linarith⟩
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at this
    exact lt_max_of_lt_left this
  · have habs : |θ - π / 3| < π / 3 := abs_lt.2 ⟨by linarith, by linarith [hθ.2]⟩
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at this
    exact lt_max_of_lt_right this

theorem eisRadial_pos {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) : 0 < eisRadial θ := by
  unfold eisRadial
  have := half_lt_max_cos hθ
  have : 0 < max (Real.cos θ) (Real.cos (θ - π / 3)) := by linarith
  positivity

theorem eisRadial_lt_one {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) : eisRadial θ < 1 := by
  unfold eisRadial
  have := half_lt_max_cos hθ
  rw [div_lt_one (by linarith)]
  linarith

theorem cos_nonneg_of_mem_eis {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - π / 3) := by
  have hpi := Real.pi_pos
  exact ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hθ.1]) hθ.2,
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2])⟩

/-- A point of the polar target lies over the rhombus iff its angle is in `[-π/6, π/2]` and its
radius is at most `eisRadial`. -/
theorem polarCoord_symm_mem_eisBaseSet_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ eisBaseSet ↔ p.2 ∈ Icc (-(π / 6)) (π / 2) ∧ p.1 ≤ eisRadial p.2 := by
  obtain ⟨r, θ⟩ := p
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [ht] at hp
  simp only [mem_prod, mem_Ioi, mem_Ioo] at hp
  obtain ⟨hr, hθ1, hθ2⟩ := hp
  have hpi := Real.pi_pos
  have hsymm : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
  have hv : r * Real.cos θ + Real.sqrt 3 * (r * Real.sin θ) = 2 * r * Real.cos (θ - π / 3) := by
    rw [cos_sub_pi_div_three']
    ring
  rw [hsymm]
  simp only [eisBaseSet, mem_setOf_eq, mem_Icc]
  rw [hv]
  constructor
  · rintro ⟨hx1, hx2, hv1, hv2⟩
    have hc1 : 0 ≤ Real.cos θ := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hr (neg_pos.2 h)]
    have hc2 : 0 ≤ Real.cos (θ - π / 3) := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hr (neg_pos.2 h)]
    have hθle : θ ≤ π / 2 := by
      by_contra h
      push_neg at h
      exact absurd hc1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith)))
    have hθge : -(π / 6) ≤ θ := by
      by_contra h
      push_neg at h
      have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt (x := π / 3 - θ) (by linarith)
        (by linarith)
      rw [← Real.cos_neg, neg_sub] at hneg
      exact absurd hc2 (not_le.2 hneg)
    refine ⟨⟨hθge, hθle⟩, ?_⟩
    have hM := half_lt_max_cos ⟨hθge, hθle⟩
    unfold eisRadial
    rw [le_div_iff₀ (by linarith)]
    rcases le_total (Real.cos θ) (Real.cos (θ - π / 3)) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · rintro ⟨hθ, hR⟩
    have hM := half_lt_max_cos hθ
    obtain ⟨hc1, hc2⟩ := cos_nonneg_of_mem_eis hθ
    unfold eisRadial at hR
    rw [le_div_iff₀ (by linarith)] at hR
    have h1 : r * Real.cos θ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_left (Real.cos θ) (Real.cos (θ - π / 3))) hr.le
      linarith
    have h2 : r * Real.cos (θ - π / 3) ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_right (Real.cos θ) (Real.cos (θ - π / 3))) hr.le
      linarith
    exact ⟨mul_nonneg hr.le hc1, h1, by nlinarith [mul_nonneg hr.le hc2], by linarith⟩

/-- The plane integral in polar coordinates. -/
theorem lintegral_eisBaseSet_polar :
    ∫⁻ z in eisBaseSet, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹)
      = ∫⁻ θ in Icc (-(π / 6)) (π / 2), ∫⁻ r in Ioc 0 (eisRadial θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
  set F : ℝ × ℝ → ENNReal := fun z => ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) with hF
  set G : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.1 / (2 * (1 - p.1 ^ 2))) with hG
  set S : Set (ℝ × ℝ) :=
    {p | p.2 ∈ Icc (-(π / 6)) (π / 2) ∧ 0 < p.1 ∧ p.1 ≤ eisRadial p.2} with hS
  have hGm : Measurable G := by fun_prop
  have hRm : Measurable eisRadial := by
    unfold eisRadial
    fun_prop
  have hSm : MeasurableSet S := by
    refine (measurableSet_Icc.preimage measurable_snd).inter ?_
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hRm.comp measurable_snd))
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  have hpt : ∀ p : ℝ × ℝ, polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • eisBaseSet.indicator F (polarCoord.symm p)) p
      = S.indicator G p := by
    intro p
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      have hr : 0 < p.1 := by
        rw [ht] at hp
        exact hp.1
      by_cases hpS : p ∈ S
      · rw [indicator_of_mem hpS]
        have hmem : polarCoord.symm p ∈ eisBaseSet :=
          (polarCoord_symm_mem_eisBaseSet_iff hp).2 ⟨hpS.1, hpS.2.2⟩
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
        have hnot : polarCoord.symm p ∉ eisBaseSet := fun h =>
          hpS ⟨((polarCoord_symm_mem_eisBaseSet_iff hp).1 h).1, hr,
            ((polarCoord_symm_mem_eisBaseSet_iff hp).1 h).2⟩
        rw [indicator_of_notMem hnot, smul_zero]
    · rw [indicator_of_notMem hp]
      have hpS : p ∉ S := by
        intro h
        apply hp
        rw [ht]
        exact ⟨h.2.1, ⟨by linarith [h.1.1, Real.pi_pos], by linarith [h.1.2, Real.pi_pos]⟩⟩
      rw [indicator_of_notMem hpS]
  calc ∫⁻ z in eisBaseSet, F z
      = ∫⁻ z, eisBaseSet.indicator F z := (lintegral_indicator measurableSet_eisBaseSet F).symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • eisBaseSet.indicator F (polarCoord.symm p) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p, S.indicator G p := by
        rw [← lintegral_indicator polarCoord.open_target.measurableSet]
        exact lintegral_congr hpt
    _ = ∫⁻ θ, ∫⁻ r, S.indicator G (r, θ) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_symm _ (hGm.indicator hSm).aemeasurable
    _ = ∫⁻ θ in Icc (-(π / 6)) (π / 2), ∫⁻ r in Ioc 0 (eisRadial θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_congr fun θ => ?_
        by_cases hθ : θ ∈ Icc (-(π / 6)) (π / 2)
        · rw [indicator_of_mem hθ, ← lintegral_indicator measurableSet_Ioc]
          refine lintegral_congr fun r => ?_
          by_cases hr : r ∈ Ioc 0 (eisRadial θ)
          · rw [indicator_of_mem hr, indicator_of_mem (show (r, θ) ∈ S from ⟨hθ, hr.1, hr.2⟩)]
          · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr ⟨h.2.1, h.2.2⟩)]
        · rw [indicator_of_notMem hθ]
          have h0 : ∀ r, S.indicator G (r, θ) = 0 := fun r =>
            indicator_of_notMem (fun h => hθ h.1) _
          simp_rw [h0]
          simp

theorem lintegral_radial_eis {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    ∫⁻ r in Ioc 0 (eisRadial θ), ENNReal.ofReal (r / (2 * (1 - r ^ 2)))
      = ENNReal.ofReal (-(1/4) * Real.log (1 - eisRadial θ ^ 2)) := by
  have hR0 := eisRadial_pos hθ
  have hR1 := eisRadial_lt_one hθ
  have hpos : ∀ r ∈ Icc (0:ℝ) (eisRadial θ), 0 < 1 - r ^ 2 := by
    intro r hr
    nlinarith [hr.1, hr.2]
  have hcont : ContinuousOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Icc 0 (eisRadial θ)) := by
    refine ContinuousOn.div continuousOn_id (by fun_prop) fun r hr => ?_
    have := hpos r hr
    positivity
  have hint : IntegrableOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Ioc 0 (eisRadial θ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1
      (ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hR0.le]))
  rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hR0.le,
    integral_radial hR0.le hR1]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  have := hpos r ⟨hr.1.le, hr.2⟩
  exact div_nonneg hr.1.le (by linarith)

theorem continuousOn_eisRadial : ContinuousOn eisRadial (Icc (-(π / 6)) (π / 2)) := by
  unfold eisRadial
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun θ hθ => ?_
  have := half_lt_max_cos hθ
  exact ne_of_gt (by linarith)

theorem continuousOn_g_eis :
    ContinuousOn (fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2)) (Icc (-(π / 6)) (π / 2)) := by
  refine continuousOn_const.mul (ContinuousOn.log ?_ fun θ hθ => ?_)
  · exact continuousOn_const.sub (continuousOn_eisRadial.pow 2)
  · have h1 := eisRadial_pos hθ
    have h2 := eisRadial_lt_one hθ
    exact ne_of_gt (by nlinarith)

theorem lintegral_Icc_g_eis :
    ∫⁻ θ in Icc (-(π / 6)) (π / 2), ENNReal.ofReal (-(1/4) * Real.log (1 - eisRadial θ ^ 2))
      = ENNReal.ofReal
          (∫ θ in (-(π / 6))..(π / 2), -(1/4) * Real.log (1 - eisRadial θ ^ 2)) := by
  have hpi := Real.pi_pos
  have hle : -(π / 6) ≤ π / 2 := by linarith
  have hint : IntegrableOn (fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2))
      (Ioc (-(π / 6)) (π / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1
      (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hle]; exact continuousOn_g_eis))
  rw [← restrict_Ioc_eq_restrict_Icc, ← ofReal_integral_eq_lintegral_ofReal hint,
    ← intervalIntegral.integral_of_le hle]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have h1 := eisRadial_pos ⟨hθ.1.le, hθ.2⟩
  have h2 := eisRadial_lt_one ⟨hθ.1.le, hθ.2⟩
  have hlog : Real.log (1 - eisRadial θ ^ 2) ≤ 0 :=
    Real.log_nonpos (by nlinarith) (by nlinarith)
  show (0:ℝ) ≤ -(1/4) * Real.log (1 - eisRadial θ ^ 2)
  linarith

/-- On `[-π/6, π/6]` the ray leaves the rhombus through `x = ½`. -/
theorem eisRadial_of_le {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 6)) :
    eisRadial θ = 1 / (2 * Real.cos θ) := by
  have hpi := Real.pi_pos
  have hle : Real.cos (θ - π / 3) ≤ Real.cos θ := by
    rw [← Real.cos_abs θ, ← Real.cos_neg (θ - π / 3), neg_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [hθ.1])
      (abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [eisRadial, max_eq_left hle]

/-- On `[π/6, π/2]` it leaves through `x + √3 y = 1`. -/
theorem eisRadial_of_ge {θ : ℝ} (hθ : θ ∈ Icc (π / 6) (π / 2)) :
    eisRadial θ = 1 / (2 * Real.cos (θ - π / 3)) := by
  have hpi := Real.pi_pos
  have hle : Real.cos θ ≤ Real.cos (θ - π / 3) := by
    rw [← Real.cos_abs (θ - π / 3)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hθ.2])
      (abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [eisRadial, max_eq_right hle]

theorem continuousOn_h_eis :
    ContinuousOn (fun θ => -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2)))
      (Icc (-(π / 6)) (π / 6)) := by
  have hpi := Real.pi_pos
  have hc : ∀ θ ∈ Icc (-(π / 6)) (π / 6), 3 / 4 ≤ Real.cos θ ^ 2 := by
    intro θ hθ
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith)
      (abs_le.2 ⟨by linarith [hθ.1], hθ.2⟩ : |θ| ≤ π / 6)
    rw [Real.cos_abs, Real.cos_pi_div_six] at h
    have hs : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, sqrt3_sq]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  refine continuousOn_const.mul (ContinuousOn.log ?_ fun θ hθ => ?_)
  · refine continuousOn_const.sub (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro θ hθ
    have := hc θ hθ
    positivity
  · have h := hc θ hθ
    have h4 : 0 < 4 * Real.cos θ ^ 2 := by positivity
    have : 1 / (4 * Real.cos θ ^ 2) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ h4 (by norm_num)]; linarith
    exact ne_of_gt (by linarith)

/-- The angular integral folds onto `[0, π/6]`. -/
theorem integral_g_fold_eis :
    ∫ θ in (-(π / 6))..(π / 2), -(1/4) * Real.log (1 - eisRadial θ ^ 2)
      = -∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) := by
  set g : ℝ → ℝ := fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2) with hg
  set h : ℝ → ℝ := fun θ => -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) with hh
  have hpi := Real.pi_pos
  have hgI : ∀ a b, -(π / 6) ≤ a → a ≤ b → b ≤ π / 2 → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    exact ContinuousOn.intervalIntegrable
      (continuousOn_g_eis.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
  have hhI : ∀ a b, -(π / 6) ≤ a → a ≤ b → b ≤ π / 6 → IntervalIntegrable h volume a b := by
    intro a b ha hab hb
    exact ContinuousOn.intervalIntegrable
      (continuousOn_h_eis.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
  have hsq : ∀ c : ℝ, (1 / (2 * c)) ^ 2 = 1 / (4 * c ^ 2) := fun c => by
    rw [div_pow, mul_pow]; norm_num
  have h1 : ∫ θ in (-(π / 6))..(π / 2), g θ
      = (∫ θ in (-(π / 6))..(π / 6), g θ) + ∫ θ in (π / 6)..(π / 2), g θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hgI _ _ le_rfl (by linarith) (by linarith))
      (hgI _ _ (by linarith) (by linarith) le_rfl)).symm
  have h2 : ∫ θ in (-(π / 6))..(π / 6), g θ = ∫ θ in (-(π / 6))..(π / 6), h θ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hg, hh, eisRadial_of_le hθ, hsq]
  have h3 : ∫ θ in (π / 6)..(π / 2), g θ = ∫ θ in (-(π / 6))..(π / 6), h θ := by
    have := intervalIntegral.integral_comp_sub_right (a := π / 6) (b := π / 2) h (π / 3)
    rw [show π / 6 - π / 3 = -(π / 6) by ring, show π / 2 - π / 3 = π / 6 by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hg, hh, eisRadial_of_ge hθ, hsq]
  have h4 : ∫ θ in (-(π / 6))..(π / 6), h θ
      = (∫ θ in (-(π / 6))..0, h θ) + ∫ θ in (0:ℝ)..(π / 6), h θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hhI _ _ le_rfl (by linarith) (by linarith))
      (hhI _ _ (by linarith) (by linarith) le_rfl)).symm
  have h5 : ∫ θ in (-(π / 6))..0, h θ = ∫ θ in (0:ℝ)..(π / 6), h θ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 6) h
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hh, Real.cos_neg]
  have h6 : ∫ θ in (0:ℝ)..(π / 6), h θ
      = -(1/4) * ∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) :=
    intervalIntegral.integral_const_mul _ _
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- The volume of the box as a single integral. -/
theorem hvol_eisBox_eq_ofReal_integral :
    hvol eisBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  rw [hvol_eisBox_eq_plane_integral, lintegral_eisBaseSet_polar,
    setLIntegral_congr_fun measurableSet_Icc fun θ hθ => lintegral_radial_eis hθ,
    lintegral_Icc_g_eis, integral_g_fold_eis]

end EisVolume

end Thurston23

open MeasureTheory in
theorem solution :
    Thurston23.hvol Thurston23.eisBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) :=
  Thurston23.hvol_eisBox_eq_ofReal_integral
