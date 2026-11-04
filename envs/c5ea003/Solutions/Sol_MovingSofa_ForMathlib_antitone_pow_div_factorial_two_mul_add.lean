-- Prove2me | solution 1 for MovingSofa.ForMathlib.antitone_pow_div_factorial_two_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:58:57.24921+00:00
-- url     : https://prove2.me/submissions/8234c78f-8537-49c4-b903-a73cb15f278c

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution {x : ℝ} (hx0 : 0 ≤ x) {a : ℕ}
    (hx : x ^ 2 ≤ ((a + 1) * (a + 2) : ℕ)) :
    Antitone fun n : ℕ ↦ x ^ (2 * n + a) / (Nat.factorial (2 * n + a) : ℝ) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  set m := 2 * n + a with hm
  have ham : a ≤ m := by omega
  have hstep : 2 * (n + 1) + a = m + 1 + 1 := by omega
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hle : x ^ 2 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    refine hx.trans ?_
    have hcast : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    push_cast
    nlinarith
  have hpow : x ^ (m + 1 + 1) = x ^ m * x * x := by ring
  rw [hstep, Nat.factorial_succ, Nat.factorial_succ, hpow,
    div_le_div_iff₀ (by positivity) hfac]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hx0 m) hfac.le) (sub_nonneg.2 hle)]
