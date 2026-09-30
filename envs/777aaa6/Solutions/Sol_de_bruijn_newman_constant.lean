-- Prove2me | solution 1 for de_bruijn_newman_constant
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T06:09:19.208871+00:00
-- url     : https://prove2.me/submissions/898f48a2-3e44-4676-b79a-577014a39fe3

import Mathlib

/-- The real term of the posted series at `t = -1/10`:
`exp(-t n² π) · (2π n² - 3) · exp(-n² π) = (2π n² - 3) · exp(-(9/10) π n²)`. -/
noncomputable def dbnTerm (n : ℕ) : ℝ :=
  (2 * Real.pi * (n : ℝ) ^ 2 - 3) * Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2)

/-- The geometric ratio used to dominate the series. -/
noncomputable def dbnR : ℝ := Real.exp (1 - 9 / 10 * Real.pi)

lemma dbnTerm_abs_le (n : ℕ) : |dbnTerm n| ≤ (2 * Real.pi + 3) * dbnR ^ n := by
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
    exact_mod_cast this
  have hexp1 : (n : ℝ) ^ 2 ≤ Real.exp ((n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp ((n : ℝ) ^ 2)]
  have hexp2 : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp ((n : ℝ) ^ 2), sq_nonneg (n : ℝ)]
  have habs : |2 * Real.pi * (n : ℝ) ^ 2 - 3| ≤ 2 * Real.pi * (n : ℝ) ^ 2 + 3 := by
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos, sq_nonneg (n : ℝ)]
  have hpos : 0 < Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2) := Real.exp_pos _
  have hneg : 1 - 9 / 10 * Real.pi < 0 := by linarith [Real.pi_gt_three]
  calc |dbnTerm n|
      = |2 * Real.pi * (n : ℝ) ^ 2 - 3| * Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2) := by
        rw [dbnTerm, abs_mul, abs_of_pos hpos]
    _ ≤ (2 * Real.pi * (n : ℝ) ^ 2 + 3) * Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2) := by
        gcongr
    _ ≤ ((2 * Real.pi + 3) * Real.exp ((n : ℝ) ^ 2)) *
          Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2) := by
        gcongr
        nlinarith [Real.pi_pos]
    _ = (2 * Real.pi + 3) * Real.exp ((1 - 9 / 10 * Real.pi) * (n : ℝ) ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (2 * Real.pi + 3) * Real.exp ((1 - 9 / 10 * Real.pi) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hn2 hneg.le)
    _ = (2 * Real.pi + 3) * dbnR ^ n := by
        rw [dbnR, ← Real.exp_nat_mul, mul_comm (1 - 9 / 10 * Real.pi)]

lemma dbnR_nonneg : 0 ≤ dbnR := (Real.exp_pos _).le

lemma dbnR_lt : dbnR < 1 / 4.4 := by
  have hexpx : (4.4 : ℝ) < Real.exp (9 / 10 * Real.pi - 1) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := 9 / 10 * Real.pi - 1)
      (by linarith [Real.pi_gt_three])
    nlinarith [Real.pi_gt_d2, sq_nonneg (9 / 10 * Real.pi - 1 - 1.826)]
  have hprod : dbnR * Real.exp (9 / 10 * Real.pi - 1) = 1 := by
    rw [dbnR, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpos : 0 < dbnR := Real.exp_pos _
  nlinarith [mul_pos (sub_pos.mpr hexpx) hpos]

lemma dbnR_lt_one : dbnR < 1 := by linarith [dbnR_lt]

lemma dbnTerm_summable : Summable dbnTerm := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one dbnR_nonneg dbnR_lt_one).mul_left (2 * Real.pi + 3)) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact dbnTerm_abs_le n

lemma dbnTerm_tsum_neg : ∑' n, dbnTerm n < 0 := by
  have ha := dbnTerm_summable
  have hr0 := dbnR_nonneg
  have hr1 := dbnR_lt_one
  have htail : ∑' n, dbnTerm (n + 1) ≤ (2 * Real.pi + 3) * (dbnR * (1 - dbnR)⁻¹) := by
    have h1 : Summable (fun n => dbnTerm (n + 1)) := (summable_nat_add_iff 1).mpr ha
    have h2 : Summable (fun n : ℕ => (2 * Real.pi + 3) * (dbnR * dbnR ^ n)) := by
      have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((2 * Real.pi + 3) * dbnR)
      simpa only [mul_assoc] using this
    calc ∑' n, dbnTerm (n + 1) ≤ ∑' n : ℕ, (2 * Real.pi + 3) * (dbnR * dbnR ^ n) := by
          refine Summable.tsum_le_tsum (fun n => ?_) h1 h2
          have := dbnTerm_abs_le (n + 1)
          rw [pow_succ'] at this
          exact (le_abs_self _).trans this
      _ = (2 * Real.pi + 3) * (dbnR * (1 - dbnR)⁻¹) := by
          rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h0 : dbnTerm 0 = -3 := by simp [dbnTerm]
  have hfin : (2 * Real.pi + 3) * (dbnR * (1 - dbnR)⁻¹) < 3 := by
    have h1r : 0 < 1 - dbnR := by linarith
    have hu : 0 < (1 - dbnR)⁻¹ := inv_pos.mpr h1r
    have hinv : (1 - dbnR)⁻¹ * (1 - dbnR) = 1 := inv_mul_cancel₀ h1r.ne'
    have key : 0 < 3 - (2 * Real.pi + 6) * dbnR := by
      nlinarith [Real.pi_lt_d2, mul_pos (sub_pos.mpr dbnR_lt) (by positivity : (0:ℝ) < 2 * Real.pi + 6)]
    nlinarith [mul_pos key hu]
  have hsplit := ha.tsum_eq_zero_add
  rw [h0] at hsplit
  linarith

theorem solution : ¬ (∃ (Lambda : ℝ),
      Lambda = 0 ∧
      ∀ (t : ℝ), t < Lambda →
        ∃ (z : ℂ), z.re > 0 ∧
          ∑' (n : ℕ), Complex.exp (-t * (n : ℂ)^2 * Real.pi) *
            (2 * Real.pi * (n : ℝ)^2 - 3) *
            Complex.exp (-(n : ℂ)^2 * Real.pi) = 0) := by
  rintro ⟨L, hL, h⟩
  subst hL
  obtain ⟨z, -, hz⟩ := h (-1 / 10) (by norm_num)
  have hz2 : ∑' (n : ℕ), ((dbnTerm n : ℝ) : ℂ) = 0 := by
    refine (tsum_congr fun n => ?_).trans hz
    have e : Complex.exp (-((-1 / 10 : ℝ) : ℂ) * (n : ℂ) ^ 2 * Real.pi) *
        Complex.exp (-(n : ℂ) ^ 2 * Real.pi) =
        ((Real.exp (-(9 / 10 * Real.pi) * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
      rw [← Complex.exp_add, Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [dbnTerm]
    push_cast at e ⊢
    linear_combination -(2 * (Real.pi : ℂ) * (n : ℂ) ^ 2 - 3) * e
  rw [← Complex.ofReal_tsum, Complex.ofReal_eq_zero] at hz2
  have := dbnTerm_tsum_neg
  linarith
