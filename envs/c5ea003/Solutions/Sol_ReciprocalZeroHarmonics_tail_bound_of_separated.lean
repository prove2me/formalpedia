-- Prove2me | solution 1 for ReciprocalZeroHarmonics.tail_bound_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:33:11.685113+00:00
-- url     : https://prove2.me/submissions/6e6b17f4-deff-463c-87df-f0cb0e75eba9

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





/-! ## Renormalised convergence -/


theorem pairedTerm_pos (g : ℕ → ℝ) (n : ℕ) : 0 < pairedTerm g n := by
  unfold pairedTerm; positivity




/-! ## A quantitative truncation error -/



/-! ## Why the renormalisation is necessary -/



open ReciprocalZeroHarmonics in
theorem solution(a : ℝ) (ha : 0 < a) (g : ℕ → ℝ)
    (hg : ∀ n : ℕ, a * ((n : ℝ) + 1) ≤ g n) (N : ℕ) (hN : 1 ≤ N) :
    ∑' n : ℕ, pairedTerm g (n + N) ≤ 1 / (a ^ 2 * N) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine Real.tsum_le_of_sum_range_le (fun n => (pairedTerm_pos g _).le) ?_
  intro M
  have step : ∀ n : ℕ, pairedTerm g (n + N)
      ≤ (1 / a ^ 2) * (1 / ((n : ℝ) + N) - 1 / (((n + 1 : ℕ) : ℝ) + N)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hb : a * ((n : ℝ) + N + 1) ≤ g (n + N) := by
      have := hg (n + N); push_cast at this ⊢; linarith
    have hap : 0 < a * ((n : ℝ) + N + 1) := by positivity
    have hsq : (a * ((n : ℝ) + N + 1)) ^ 2 ≤ g (n + N) ^ 2 := by nlinarith
    have h1 : (1 / a ^ 2) * (1 / ((n : ℝ) + N) - 1 / (((n + 1 : ℕ) : ℝ) + N))
        = 1 / (a ^ 2 * (((n : ℝ) + N) * ((n : ℝ) + N + 1))) := by
      push_cast; field_simp; ring
    unfold pairedTerm
    rw [h1]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  calc ∑ n ∈ Finset.range M, pairedTerm g (n + N)
      ≤ ∑ n ∈ Finset.range M, (1 / a ^ 2) * (1 / ((n : ℝ) + N) - 1 / (((n + 1 : ℕ) : ℝ) + N)) :=
        Finset.sum_le_sum fun n _ => step n
    _ = (1 / a ^ 2) * ∑ n ∈ Finset.range M,
          (1 / ((n : ℝ) + N) - 1 / (((n + 1 : ℕ) : ℝ) + N)) := by rw [Finset.mul_sum]
    _ = (1 / a ^ 2) * (1 / (((0 : ℕ) : ℝ) + N) - 1 / ((M : ℝ) + N)) := by
        rw [Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + N)) M]
    _ ≤ 1 / (a ^ 2 * N) := by
        have h2 : (0 : ℝ) < (M : ℝ) + N := by linarith [Nat.cast_nonneg (α := ℝ) M]
        have h3 : (0 : ℝ) < 1 / ((M : ℝ) + N) := by positivity
        have h4 : (1 / a ^ 2) * (1 / (N : ℝ) - 1 / ((M : ℝ) + N)) ≤ (1 / a ^ 2) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        calc (1 / a ^ 2) * (1 / (((0 : ℕ) : ℝ) + N) - 1 / ((M : ℝ) + N))
            = (1 / a ^ 2) * (1 / (N : ℝ) - 1 / ((M : ℝ) + N)) := by norm_num
          _ ≤ (1 / a ^ 2) * (1 / (N : ℝ)) := h4
          _ = 1 / (a ^ 2 * N) := by field_simp
