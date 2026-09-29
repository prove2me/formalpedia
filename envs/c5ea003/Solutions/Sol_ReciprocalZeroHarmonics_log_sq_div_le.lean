-- Prove2me | solution 1 for ReciprocalZeroHarmonics.log_sq_div_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:31:48.5099+00:00
-- url     : https://prove2.me/submissions/b5e14651-be41-4ab1-9413-8f82a241bedc

-- Sol generated from Algebra/ReciprocalZeroHarmonics/Convergence.lean
import Mathlib
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Convergence
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Core

/-!
# Reciprocal-Zero Harmonics III: renormalised convergence and a quantitative tail bound

Direction 1 of the programme asks for an explicit renormalisation under which the
multiplicity-sensitive, conjugate-symmetric sum `H(T) = Σ_{|Im ρ| ≤ T} 1/ρ` converges, with an
error term controlled by zero counting.  `Core.lean` supplies the renormalisation: conjugate
pairing replaces `1/ρ + 1/ρ̄` by the positive real number `1/(1/4 + t²)`.  This file supplies
the analytic half.

Throughout, `g : ℕ → ℝ` is an increasing enumeration of the positive ordinates of the zeros.
The Riemann–von Mangoldt formula `N(T) = (T/2π)·log(T/2πe) + O(log T)` is equivalent to a lower
bound of the shape `g n ≥ a·(n+1)/log(n+2)`, and this is exactly the hypothesis we take as
input; no unproved analytic statement about `ζ` is assumed anywhere.

## Main results

* `summable_renormalized_of_rvm` — **renormalised convergence.**  Under the
  Riemann–von Mangoldt-type lower bound `g n ≥ a·(n+1)/log(n+2)` (`a > 0`) the paired series
  `Σ_n 1/(1/4 + g(n)²)` converges absolutely.
* `tendsto_pairedHarmonic` — consequently the conjugate-paired window sums
  `Re H(Z_N) = Σ_{n<N} 1/(1/4 + g(n)²)` of `Core.harmonicSum` converge to a finite limit; this is
  the renormalised value of `H(T)`.
* `tail_bound_of_separated` — **quantitative error term.**  Under the stronger separation
  hypothesis `g n ≥ a·(n+1)` the truncation error is explicit:
  `Σ_{n ≥ N} 1/(1/4 + g(n)²) ≤ 1/(a²N)`.
* `not_summable_unpaired` — **the renormalisation is necessary.**  If the ordinates do not grow
  faster than linearly (`g n ≤ b·(n+1)`), the unpaired series `Σ_n 1/g(n)` diverges.  Absolute
  convergence of `Σ 1/ρ` genuinely fails; only the conjugate-paired sum converges.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** Conjugate pairing gains one power of the ordinate
  (`1/ρ + 1/ρ̄ ≍ 1/t²` instead of `1/t`), and zero counting shows `t ≍ n/log n`; the paired sum
  should therefore converge while the unpaired one diverges.
* **Experiment (Experimenter).** Convergence: `1/(1/4+g²) ≤ log(n+2)²/(a²(n+1)²)` and
  `log x ≤ 4x^{1/4}` (from `log y ≤ y - 1` applied to `y = x^{1/4}`) give the summable majorant
  `32·(n+1)^{-3/2}`.  Divergence: comparison with the harmonic series.  The error term is a
  telescoping estimate `1/(n+N)(n+N+1) = 1/(n+N) - 1/(n+N+1)`.
* **Analysis (Analyst).** Both phenomena are quantitative expressions of the same fact: the
  ordinate sequence grows essentially linearly.  The gap between the two theorems
  (`Σ 1/g` diverges, `Σ 1/(1/4+g²)` converges) is precisely the analytic content of the
  conjugation principle: the renormalisation is not cosmetic.
* **Critique (Critic).** No statement is vacuous: `summable_renormalized_of_rvm` and
  `not_summable_unpaired` have overlapping hypotheses (e.g. `g n = n+1` satisfies both), so the
  two conclusions apply simultaneously to genuine sequences, showing the contrast is real.
-/

open ReciprocalZeroHarmonics

open Filter

/-! ## A summable majorant -/

/-- `log x ≤ 4·x^{1/4}` for `x > 0`, obtained from `log y ≤ y - 1` at `y = x^{1/4}`. -/
theorem log_le_four_rpow (x : ℝ) (hx : 0 < x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have h1 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx _)
  rw [Real.log_rpow hx] at h1
  nlinarith [Real.rpow_pos_of_pos hx (1 / 4 : ℝ)]

theorem log_sq_le (n : ℕ) : Real.log ((n : ℝ) + 2) ^ 2 ≤ 16 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
  have hx : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h := log_le_four_rpow ((n : ℝ) + 2) hx
  have hpos : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h2 : Real.log ((n : ℝ) + 2) ^ 2 ≤ (4 * ((n : ℝ) + 2) ^ (1 / 4 : ℝ)) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ^ 2 ≤ (4 * ((n : ℝ) + 2) ^ (1 / 4 : ℝ)) ^ 2 := h2
    _ = 16 * (((n : ℝ) + 2) ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ = 16 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (((n : ℝ) + 2) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx)]
        norm_num



/-! ## Renormalised convergence -/






/-! ## A quantitative truncation error -/



/-! ## Why the renormalisation is necessary -/



open ReciprocalZeroHarmonics in
theorem solution(n : ℕ) :
    Real.log ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 2 ≤ 32 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    have h4 : ((n : ℝ) + 2) ≤ 4 * ((n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    calc ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (4 * ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      _ = 4 ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by norm_num) (le_of_lt h1)
      _ = 2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by norm_num
  have key : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) / ((n : ℝ) + 1) ^ 2 = 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    rw [show ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
      ← Real.rpow_sub h1, eq_div_iff (by positivity), ← Real.rpow_add h1]
    norm_num
  calc Real.log ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 2
      ≤ (16 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) / ((n : ℝ) + 1) ^ 2 := by
        gcongr
        exact log_sq_le n
    _ ≤ (16 * (2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ))) / ((n : ℝ) + 1) ^ 2 := by gcongr
    _ = 32 * (((n : ℝ) + 1) ^ (1 / 2 : ℝ) / ((n : ℝ) + 1) ^ 2) := by ring
    _ = 32 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by rw [key]; ring
