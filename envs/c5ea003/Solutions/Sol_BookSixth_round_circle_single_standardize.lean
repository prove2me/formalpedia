-- Prove2me | solution 1 for BookSixth.round_circle_single_standardize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T05:07:04.756395+00:00
-- url     : https://prove2.me/submissions/8c5b971f-2261-42c4-a5ef-d71f6deb10d3

import Mathlib
import Definitions.Def_BookSixth

theorem iso_basic_57b (A B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hA : Continuous (fun p : ℝ × (Fin 3 → ℝ) => A p.1 p.2))
    (hB : Continuous (fun p : ℝ × (Fin 3 → ℝ) => B p.1 p.2))
    (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
    (h0 : ∀ x, A 0 x = x) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = A 1 x) := by
  refine ⟨fun t =>
    { toFun := A t, invFun := B t, left_inv := hBA t, right_inv := hAB t,
      continuous_toFun := hA.comp (continuous_const.prodMk continuous_id),
      continuous_invFun := hB.comp (continuous_const.prodMk continuous_id) },
    hA, hB, h0, fun x => rfl⟩

theorem iso_comp_57b (F G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hF : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x))
    (hG : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = G x)) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = G (F x)) := by
  obtain ⟨H1, c1, d1, e1, f1⟩ := hF
  obtain ⟨H2, c2, d2, e2, f2⟩ := hG
  refine ⟨fun t => (H1 t).trans (H2 t), ?_, ?_, ?_, ?_⟩
  · exact c2.comp (continuous_fst.prodMk c1)
  · exact d1.comp (continuous_fst.prodMk d2)
  · intro x; simp [e1, e2]
  · intro x; simp [f1, f2]

theorem angle_57b (a b : ℝ) :
    ∃ θ : ℝ, Real.sin θ * a + Real.cos θ * b = 0 ∧ 0 ≤ Real.cos θ * a - Real.sin θ * b := by
  by_cases h : a = 0 ∧ b = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp [h.1, h.2]
  · have hz : (⟨a, b⟩ : ℂ) ≠ 0 := by
      intro hz
      apply h
      exact ⟨congrArg Complex.re hz, congrArg Complex.im hz⟩
    refine ⟨-Complex.arg ⟨a, b⟩, ?_, ?_⟩
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      ring
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      have : 0 ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ :=
        div_nonneg (by nlinarith [mul_self_nonneg a, mul_self_nonneg b]) (norm_nonneg _)
      calc (0 : ℝ) ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ := this
        _ = _ := by ring

theorem iso_rot01_57b (θ : ℝ) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = ![Real.cos θ * x 0 - Real.sin θ * x 1,
                      Real.sin θ * x 0 + Real.cos θ * x 1, x 2]) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_57b
    (fun t x => ![Real.cos (t * θ) * x 0 - Real.sin (t * θ) * x 1,
                  Real.sin (t * θ) * x 0 + Real.cos (t * θ) * x 1, x 2])
    (fun t x => ![Real.cos (t * θ) * x 0 + Real.sin (t * θ) * x 1,
                  -(Real.sin (t * θ) * x 0) + Real.cos (t * θ) * x 1, x 2])
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 0 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 0 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro x
      funext i
      fin_cases i <;> simp)
  exact ⟨H, h1, h2, h3, fun x => by rw [h4]; simp⟩

theorem iso_rot02_57b (θ : ℝ) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1,
                      Real.sin θ * x 0 + Real.cos θ * x 2]) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_57b
    (fun t x => ![Real.cos (t * θ) * x 0 - Real.sin (t * θ) * x 2, x 1,
                  Real.sin (t * θ) * x 0 + Real.cos (t * θ) * x 2])
    (fun t x => ![Real.cos (t * θ) * x 0 + Real.sin (t * θ) * x 2, x 1,
                  -(Real.sin (t * θ) * x 0) + Real.cos (t * θ) * x 2])
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 0 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 2 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 0 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 2 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro x
      funext i
      fin_cases i <;> simp)
  exact ⟨H, h1, h2, h3, fun x => by rw [h4]; simp⟩

theorem iso_rot12_57b (θ : ℝ) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
                      Real.sin θ * x 1 + Real.cos θ * x 2]) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_57b
    (fun t x => ![x 0, Real.cos (t * θ) * x 1 - Real.sin (t * θ) * x 2,
                  Real.sin (t * θ) * x 1 + Real.cos (t * θ) * x 2])
    (fun t x => ![x 0, Real.cos (t * θ) * x 1 + Real.sin (t * θ) * x 2,
                  -(Real.sin (t * θ) * x 1) + Real.cos (t * θ) * x 2])
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 2 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * θ)
      · linear_combination x 2 * Real.cos_sq_add_sin_sq (t * θ))
    (by
      intro x
      funext i
      fin_cases i <;> simp)
  exact ⟨H, h1, h2, h3, fun x => by rw [h4]; simp⟩

theorem iso_affine_57b (c : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = r⁻¹ • (x - c)) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_57b
    (fun t x => Real.exp (-(t * Real.log r)) • (x - t • c))
    (fun t x => Real.exp (t * Real.log r) • x + t • c)
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      simp only [add_sub_cancel_right, smul_smul, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, one_smul])
    (by
      intro t x
      simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul,
        sub_add_cancel])
    (by
      intro x
      simp)
  refine ⟨H, h1, h2, h3, fun x => ?_⟩
  rw [h4]
  simp [Real.exp_neg, Real.exp_log hr]

theorem iso_translate_57b (a : Fin 3 → ℝ) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = x + a) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_57b
    (fun t x => x + t • a) (fun t x => x - t • a)
    (by fun_prop) (by fun_prop)
    (by intro t x; simp)
    (by intro t x; simp)
    (by intro x; simp)
  exact ⟨H, h1, h2, h3, fun x => by rw [h4]; simp⟩

set_option maxHeartbeats 4000000 in
open BookSixth in
theorem solution (D : Set Space3)
    (hroundD : RoundCircle D) (k : ℕ) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (H 1) '' D = standardCircle k := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hD⟩ := hroundD
  simp only [Fin.sum_univ_three] at hu hv huv
  obtain ⟨θ1, h1a, h1b⟩ := angle_57b (u 0) (u 1)
  obtain ⟨θ2, h2a, h2b⟩ := angle_57b (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) (u 2)
  obtain ⟨θ3, h3a, h3b⟩ := angle_57b (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
  -- norms along the chain for u
  have p1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    linear_combination (u 0 ^ 2 + u 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) ^ 2
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have hρ2sq : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      = 1 := by
    linear_combination p2 + p1 + hu
      - (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) * h2a
      - (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * h1a
  have hρ2 : Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1 := by
    have hm : ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) - 1)
        * ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) + 1)
        = 0 := by linear_combination hρ2sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  -- inner products along the chain
  have q1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      = u 0 * v 0 + u 1 * v 1 := by
    linear_combination (u 0 * v 0 + u 1 * v 1) * Real.cos_sq_add_sin_sq θ1
  have q2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2)
        * (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2)
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2)
        * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + u 2 * v 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1)
      * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + u 2 * v 2) * Real.cos_sq_add_sin_sq θ2
  have hd0 : Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0 := by
    linear_combination q2 + q1 + huv
      - (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) * h2a
      - (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) * h1a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hρ2
  -- norms along the chain for v
  have p1v : (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2
      + (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2v : (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2
      = (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have p3 : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      + (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      = (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2 := by
    linear_combination ((Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2)
      * Real.cos_sq_add_sin_sq θ3
  have hρ3sq : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2 = 1 := by
    linear_combination p3 + p2v + p1v + hv
      - (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) * h3a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hd0
  have hρ3 : Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2) = 1 := by
    have hm : ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) - 1) * ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) + 1) = 0 := by linear_combination hρ3sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  obtain ⟨H, hc1, hc2, h0, h1⟩ := iso_comp_57b _ _ (iso_comp_57b _ _ (iso_comp_57b _ _
      (iso_comp_57b _ _ (iso_affine_57b c r hr) (iso_rot01_57b θ1)) (iso_rot02_57b θ2))
      (iso_rot12_57b θ3)) (iso_translate_57b ![3 * (k : ℝ), 0, 0])
  refine ⟨H, hc1, hc2, h0, ?_⟩
  have key : ∀ t : ℝ, H 1 (c + (r * Real.cos t) • u + (r * Real.sin t) • v)
      = ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0] := by
    intro t
    have hy : r⁻¹ • (c + (r * Real.cos t) • u + (r * Real.sin t) • v - c)
        = Real.cos t • u + Real.sin t • v := by
      rw [add_assoc, add_sub_cancel_left, smul_add, smul_smul, smul_smul, ← mul_assoc,
        ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, one_mul]
    rw [h1]
    simp only [hy]
    funext i
    fin_cases i <;> simp
    · linear_combination Real.cos t * hρ2 + Real.sin t * hd0
    · linear_combination Real.cos t * (Real.cos θ3 * h1a - Real.sin θ3 * h2a)
        + Real.sin t * hρ3
    · linear_combination Real.cos t * (Real.sin θ3 * h1a + Real.cos θ3 * h2a)
        + Real.sin t * h3a
  rw [hD, ← Set.range_comp]
  unfold standardCircle
  congr 1
  funext t
  exact key t
