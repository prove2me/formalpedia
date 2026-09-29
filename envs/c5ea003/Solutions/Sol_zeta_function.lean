-- Prove2me | solution 1 for zeta_function
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:21:38.043078+00:00
-- url     : https://prove2.me/submissions/cd7e38b5-e936-4ee2-bc44-a13f0c83f6aa

-- Sol generated from Novelty/CharacterClassContradiction.lean
import Mathlib
import Definitions.Def_Novelty_CharacterClassContradiction

/-!
# The Character Class Contradiction

This file formalises a small "zeta-function" computation for the rank-one matrix

`A = !![1,1;1,1]`

over `ℚ`, and uses it to refute the *naive expectation* that the point counts
`Nᵣ = trace (Aʳ)` should vanish for all `r ≠ 1`.

The matrix `A` has eigenvalues `0` and `2`, so `trace (Aʳ) = 0ʳ + 2ʳ`.  For
`r ≥ 1` this equals `2ʳ`, while for `r = 0` it equals `trace (1) = 2 ≠ 2⁰ = 1`.

## Main results

* `A_mul_A_eq_two_mul_A` — `A * A = 2 • A`.
* `trace_pow_two_shift` — `trace (Aʳ) = 2ʳ` for `r ≥ 1`.
* `det_one_sub_t_mul_A` — `det (1 - t • A) = 1 - 2 t`.
* `zeta_function` — the zeta series `Z t = exp (∑ Nᵣ tʳ / r)` equals
  `1 / (1 - 2 t)` (for `|t| < 1/2`, where the defining series converges).
* `naive_expectation_false` — it is **not** the case that `trace (Aʳ) = 0`
  for all `r ≠ 1`.

## Implementation notes

* The matrix-multiplication notation `⬝` used in older Mathlib has been removed;
  square-matrix multiplication is the ordinary `*`, which is what we use.
* `trace_pow_two_shift` is stated with the hypothesis `1 ≤ r`.  This is necessary:
  at `r = 0` the literal identity `trace (A⁰) = 2⁰` is false because
  `trace (1) = 2` while `2⁰ = 1`.  The zeta series only ever sees the `r ≥ 1`
  values (the `r = 0` summand is killed by the `/ r` with `r = 0`).
* `zeta_function` carries the hypothesis `|t| < 1/2`, the radius of convergence of
  the defining logarithmic series; outside this disc the series diverges, so the
  identity cannot hold for *all* rational `t`.
-/

open Matrix


/-- `A * A = 2 • A`: the defining quadratic relation of the rank-one matrix `A`. -/
theorem A_mul_A_eq_two_mul_A : A * A = (2 : ℚ) • A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The powers of `A` are scalar multiples of `A`: `A ^ (n+1) = 2 ^ n • A`. -/
theorem A_pow_succ (n : ℕ) : A ^ (n + 1) = (2 ^ n : ℚ) • A := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Matrix.smul_mul, A_mul_A_eq_two_mul_A, smul_smul]
    congr 1
    ring

/-- The trace of `A` is `2`. -/
theorem trace_A : A.trace = (2 : ℚ) := by
  simp [Matrix.trace_fin_two, A]
  norm_num

/-- For `r ≥ 1`, `trace (A ^ r) = 2 ^ r`.

The hypothesis `1 ≤ r` is essential: at `r = 0` we have `trace (A ^ 0) =
trace 1 = 2 ≠ 1 = 2 ^ 0`. -/
theorem trace_pow_two_shift (r : ℕ) (hr : 1 ≤ r) : (A ^ r).trace = 2 ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [A_pow_succ, Matrix.trace_smul, trace_A, smul_eq_mul, pow_succ]






theorem solution(t : ℚ) (ht : |(t : ℝ)| < 1 / 2) :
    Z t = 1 / (1 - 2 * (t : ℝ)) := by
  set x : ℝ := 2 * (t : ℝ) with hx
  have hxlt : |x| < 1 := by rw [hx, abs_mul, abs_two]; linarith
  -- Each `r ≥ 1` summand equals the corresponding term of the `-log (1 - x)` series.
  have hfun : ∀ n : ℕ,
      (N (n + 1) : ℝ) * (t : ℝ) ^ (n + 1) / (n + 1) = x ^ (n + 1) / ((n : ℝ) + 1) := by
    intro n
    have hN : N (n + 1) = (2 : ℚ) ^ (n + 1) :=
      trace_pow_two_shift (n + 1) (by omega)
    rw [hN, hx, mul_pow]
    push_cast
    ring
  -- Power series for `-log (1 - x)`.
  have hs0 : HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hxlt
  have hs1 : HasSum (fun n : ℕ => (N (n + 1) : ℝ) * (t : ℝ) ^ (n + 1) / (n + 1))
      (-Real.log (1 - x)) :=
    hs0.congr_fun (fun n => hfun n)
  -- Reinsert the (vanishing) `r = 0` term.
  have hsfull : HasSum (fun r : ℕ => (N r : ℝ) * (t : ℝ) ^ r / r) (-Real.log (1 - x)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using hs1
  rw [Z, hsfull.tsum_eq, Real.exp_neg,
    Real.exp_log (by linarith [abs_lt.mp hxlt |>.2]), hx]
  field_simp
