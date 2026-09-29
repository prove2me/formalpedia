-- Prove2me | solution 1 for mme_112_squared_extraction_entropy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:37:13.824153+00:00
-- url     : https://prove2.me/submissions/9a45983b-beec-4000-b4ef-8998446ea388

import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear

open Filter

private theorem behrend_log_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      200 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  linarith


/-- The two directional family capacities and the squared extraction bound
attain their combined entropy rate after all sublinear losses. Zero outer
count is allowed as long as the total count is positive. -/
theorem solution
    (l g : ℕ) (hD : 0 < l + g) (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N := (l + g) * m
      let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
      ∀ A H copies : ℕ, 0 < A → 0 < H → H ≤ 4 ^ N →
        ((Nat.choose (2 * N) (l * m) *
          Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) *
          Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) →
        (Nat.choose (2 * N) N : ℝ) *
          Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) →
        ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤
            (copies : ℝ) →
        ((4 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
            Real.log (copies : ℝ) := by
  have he := mme_complete_split_112_outer_star_entropy_rate l g hD C
    (delta / 6) (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C (delta / 6) (by positivity))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (mme_log_sqrt_loss_eventually_le_linear 0 400 0 (2 * delta) (by positivity))
  filter_upwards [he, eventually_ge_atTop (max n₀ n₁)] with m hm hmn
  dsimp only at hm ⊢
  intro A H copies hA hH hHbound houter hjoint hcount
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hmN : m ≤ (l + g) * m := by
    simpa using Nat.mul_le_mul_right m hD
  have hlogA := hm (A : ℝ) hAr houter
  have hlogAH := hn₀ ((l + g) * m) (by omega)
    ((A : ℝ) * (H : ℝ)) (mul_pos hAr hHr)
    (by simpa only [mul_assoc] using hjoint)
  have hbudget := hn₁ ((l + g) * m) (by omega)
  have hloss := behrend_log_loss_bound ((l + g) * m) H hHbound
  have hpositive : 0 < ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 := by
    positivity
  have hlog := Real.log_le_log hpositive hcount
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  rw [Real.log_mul hAr.ne' hHr.ne'] at hlogAH
  simp only [zero_mul, zero_add, add_zero] at hbudget
  push_cast at hlogA hlogAH hlog hbudget hloss ⊢
  nlinarith only [hlogA, hlogAH, hlog, hbudget, hloss]


#print axioms solution
