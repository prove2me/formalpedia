-- Prove2me | solution 1 for lean_workbook_plus_72234
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:27.780506+00:00
-- url     : https://prove2.me/submissions/cb169fc0-5d76-4f6b-853f-bcbfcbdb40df

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Filter
open scoped Topology

noncomputable def twoPoleKernel (a b z : ℂ) : ℂ := ((z - a) * (z - b))⁻¹

theorem twoPoleKernel_meromorphic (a b z : ℂ) : MeromorphicAt (twoPoleKernel a b) z := by
  exact ((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.sub analyticAt_const)).meromorphicAt.inv

theorem twoPoleKernel_analytic {a b z : ℂ} (ha : z ≠ a) (hb : z ≠ b) :
    AnalyticAt ℂ (twoPoleKernel a b) z := by
  exact ((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.sub analyticAt_const)).inv (mul_ne_zero (sub_ne_zero.mpr ha)
      (sub_ne_zero.mpr hb))

theorem twoPoleKernel_order_left {a b : ℂ} (hab : a ≠ b) :
    meromorphicOrderAt (twoPoleKernel a b) a = (-1 : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (twoPoleKernel_meromorphic a b a)).mpr
  refine ⟨fun z => (z - b)⁻¹, (analyticAt_id.sub analyticAt_const).inv
    (sub_ne_zero.mpr hab), inv_ne_zero (sub_ne_zero.mpr hab), ?_⟩
  filter_upwards with z
  simp only [twoPoleKernel, zpow_neg_one, smul_eq_mul, mul_inv]

theorem twoPoleKernel_swap (a b : ℂ) : twoPoleKernel a b = twoPoleKernel b a := by
  funext z
  simp only [twoPoleKernel, mul_comm]

theorem twoPoleKernel_order_right {a b : ℂ} (hab : a ≠ b) :
    meromorphicOrderAt (twoPoleKernel a b) b = (-1 : WithTop ℤ) := by
  rw [twoPoleKernel_swap]
  exact twoPoleKernel_order_left hab.symm

theorem twoPoleKernel_order_away {a b z : ℂ} (ha : z ≠ a) (hb : z ≠ b) :
    meromorphicOrderAt (twoPoleKernel a b) z = 0 := by
  have h := twoPoleKernel_analytic ha hb
  rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr]
  · rfl
  · exact inv_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb))

theorem twoPoleKernel_residue_limit_left {a b : ℂ} (hab : a ≠ b) :
    Tendsto (fun z => (z - a) * twoPoleKernel a b z) (𝓝[≠] a) (𝓝 (a - b)⁻¹) := by
  have hc : ContinuousAt (fun z : ℂ => (z - b)⁻¹) a :=
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hab)
  apply hc.continuousWithinAt.tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  simp only [twoPoleKernel, mul_inv, ← mul_assoc, mul_inv_cancel₀ hza, one_mul]

theorem twoPoleKernel_residue_limit_right {a b : ℂ} (hab : a ≠ b) :
    Tendsto (fun z => (z - b) * twoPoleKernel a b z) (𝓝[≠] b) (𝓝 (b - a)⁻¹) := by
  rw [twoPoleKernel_swap]
  exact twoPoleKernel_residue_limit_left hab.symm

theorem twoPoleKernel_partial_fractions {a b z : ℂ} (hab : a ≠ b)
    (ha : z ≠ a) (hb : z ≠ b) :
    twoPoleKernel a b z = (a - b)⁻¹ * ((z - a)⁻¹ - (z - b)⁻¹) := by
  unfold twoPoleKernel
  have h₁ := sub_ne_zero.mpr hab
  have h₂ := sub_ne_zero.mpr ha
  have h₃ := sub_ne_zero.mpr hb
  field_simp
  ring

theorem twoPoleKernel_poles_exactly {a b : ℂ} (hab : a ≠ b) (z : ℂ) :
    meromorphicOrderAt (twoPoleKernel a b) z < 0 ↔ z = a ∨ z = b := by
  by_cases ha : z = a
  · subst z
    rw [twoPoleKernel_order_left hab]
    norm_num
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by decide)
  by_cases hb : z = b
  · subst z
    rw [twoPoleKernel_order_right hab]
    norm_num
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by decide)
  rw [twoPoleKernel_order_away ha hb]
  simp [ha, hb]

theorem twoPoleKernel_unbounded_at_poles {a b : ℂ} (hab : a ≠ b) {z : ℂ}
    (hz : z = a ∨ z = b) :
    Tendsto (fun w => ‖twoPoleKernel a b w‖) (𝓝[≠] z) atTop := by
  rw [tendsto_norm_atTop_iff_cobounded]
  exact tendsto_cobounded_of_meromorphicOrderAt_neg
    ((twoPoleKernel_poles_exactly hab z).mpr hz)

theorem twoPoleKernel_no_continuous_extension {a b z : ℂ} (hab : a ≠ b)
    (hz : z = a ∨ z = b) {g : ℂ → ℂ}
    (hEq : twoPoleKernel a b =ᶠ[𝓝[≠] z] g) : ¬ ContinuousAt g z := by
  intro hg
  have hm := (twoPoleKernel_meromorphic a b z).congr hEq
  have hNonneg := (hm.analyticAt hg).meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hEq] at hNonneg
  exact (not_le_of_gt ((twoPoleKernel_poles_exactly hab z).mpr hz)) hNonneg

theorem reciprocal_quadratic_kernel : (fun z : ℂ => (z ^ 2 - 1)⁻¹) =
    twoPoleKernel 1 (-1) := by
  funext z
  unfold twoPoleKernel
  congr 1
  ring

theorem reciprocal_quadratic_orders (z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => (w ^ 2 - 1)⁻¹) z =
      if z = 1 ∨ z = -1 then (-1 : WithTop ℤ) else 0 := by
  rw [reciprocal_quadratic_kernel]
  by_cases h₁ : z = 1
  · subst z
    rw [twoPoleKernel_order_left (by norm_num)]
    simp
  by_cases h₂ : z = -1
  · subst z
    rw [twoPoleKernel_order_right (by norm_num)]
    simp
  rw [twoPoleKernel_order_away h₁ h₂]
  simp [h₁, h₂]

theorem reciprocal_quadratic_analytic_iff (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (w ^ 2 - 1)⁻¹) z ↔ z ≠ 1 ∧ z ≠ -1 := by
  constructor
  · intro h
    have hn := h.meromorphicOrderAt_nonneg
    rw [reciprocal_quadratic_orders] at hn
    by_contra hbad
    have hp : z = 1 ∨ z = -1 := by tauto
    rw [if_pos hp] at hn
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hn
    have hImpossible : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hn
    omega
  · rintro ⟨h₁, h₂⟩
    rw [reciprocal_quadratic_kernel]
    exact twoPoleKernel_analytic h₁ h₂

theorem reciprocal_quadratic_residue_limits :
    Tendsto (fun z : ℂ => (z - 1) / (z ^ 2 - 1)) (𝓝[≠] 1) (𝓝 (1 / 2)) ∧
    Tendsto (fun z : ℂ => (z + 1) / (z ^ 2 - 1)) (𝓝[≠] (-1)) (𝓝 (-1 / 2)) := by
  have hL := twoPoleKernel_residue_limit_left (a := (1 : ℂ)) (b := -1) (by norm_num)
  have hR := twoPoleKernel_residue_limit_right (a := (1 : ℂ)) (b := -1) (by norm_num)
  rw [← reciprocal_quadratic_kernel] at hL hR
  constructor
  · convert hL using 1 <;> norm_num [div_eq_mul_inv]
  · convert hR using 1 <;> norm_num [div_eq_mul_inv]

theorem reciprocal_quadratic_poles_unbounded {z : ℂ} (hz : z = 1 ∨ z = -1) :
    Tendsto (fun w : ℂ => ‖(w ^ 2 - 1)⁻¹‖) (𝓝[≠] z) atTop := by
  have h := twoPoleKernel_unbounded_at_poles (a := (1 : ℂ)) (b := -1) (by norm_num) hz
  rwa [← reciprocal_quadratic_kernel] at h

theorem solution : ∀ z : ℂ, (z ^ 2 - 1)⁻¹ = 0 ↔ z = 1 ∨ z = -1 := by
  intro z
  rw [inv_eq_zero, show z ^ 2 - 1 = (z - 1) * (z + 1) by ring, mul_eq_zero]
  simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]

#print axioms twoPoleKernel
#print axioms twoPoleKernel_meromorphic
#print axioms twoPoleKernel_analytic
#print axioms twoPoleKernel_order_left
#print axioms twoPoleKernel_swap
#print axioms twoPoleKernel_order_right
#print axioms twoPoleKernel_order_away
#print axioms twoPoleKernel_residue_limit_left
#print axioms twoPoleKernel_residue_limit_right
#print axioms twoPoleKernel_partial_fractions
#print axioms twoPoleKernel_poles_exactly
#print axioms twoPoleKernel_unbounded_at_poles
#print axioms twoPoleKernel_no_continuous_extension
#print axioms reciprocal_quadratic_kernel
#print axioms reciprocal_quadratic_orders
#print axioms reciprocal_quadratic_analytic_iff
#print axioms reciprocal_quadratic_residue_limits
#print axioms reciprocal_quadratic_poles_unbounded
#print axioms solution
