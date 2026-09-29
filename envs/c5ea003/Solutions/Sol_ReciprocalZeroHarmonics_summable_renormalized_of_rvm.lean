-- Prove2me | solution 1 for ReciprocalZeroHarmonics.summable_renormalized_of_rvm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:33:10.889213+00:00
-- url     : https://prove2.me/submissions/3d7784c8-c71d-4b1b-85e2-1a628c744df6

-- Sol generated from Algebra/ReciprocalZeroHarmonics/Convergence.lean
import Mathlib
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Convergence
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Core
import Theorems.Thm_ReciprocalZeroHarmonics_log_sq_div_le

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




/-- The Riemann–von Mangoldt majorant `log(n+2)²/(n+1)²` is summable. -/
theorem summable_log_sq_div :
    Summable fun n : ℕ => Real.log ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hs : Summable fun n : ℕ => 32 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    simpa using ((summable_nat_add_iff 1).mpr h).mul_left 32
  exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => log_sq_div_le n) hs

/-! ## Renormalised convergence -/


theorem pairedTerm_pos (g : ℕ → ℝ) (n : ℕ) : 0 < pairedTerm g n := by
  unfold pairedTerm; positivity




/-! ## A quantitative truncation error -/



/-! ## Why the renormalisation is necessary -/



open ReciprocalZeroHarmonics in
theorem solution(a : ℝ) (ha : 0 < a) (g : ℕ → ℝ)
    (hg : ∀ n : ℕ, a * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 2) ≤ g n) :
    Summable (pairedTerm g) := by
  refine Summable.of_nonneg_of_le (fun n => (pairedTerm_pos g n).le) (fun n => ?_)
    ((summable_log_sq_div).mul_left (1 / a ^ 2))
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  set c : ℝ := a * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcg : c ≤ g n := hg n
  have hcsq : c ^ 2 ≤ g n ^ 2 := by nlinarith
  have hcsq' : c ^ 2 = a ^ 2 * ((n : ℝ) + 1) ^ 2 / Real.log ((n : ℝ) + 2) ^ 2 := by
    rw [hc, div_pow]; ring
  have hmaj : (1 / a ^ 2) * (Real.log ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 2)
      = 1 / (a ^ 2 * ((n : ℝ) + 1) ^ 2 / Real.log ((n : ℝ) + 2) ^ 2) := by
    field_simp
  unfold pairedTerm
  rw [hmaj]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [← hcsq']
  nlinarith
