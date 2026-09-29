-- Prove2me | Theorems.Thm_ReciprocalZeroHarmonics_not_summable_unpaired
-- name    : ReciprocalZeroHarmonics.not_summable_unpaired
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:55:46.639765+00:00
-- url     : https://prove2.me/theorems/8d63b675-3f63-48b5-bba4-30b2960e262b
-- title:
--   Divergence of the unpaired sum.
-- statement:
--   **Divergence of the unpaired sum.**  If the ordinates grow at most linearly then
--   `Σ_n 1/g(n)` diverges: the sum `Σ_ρ 1/ρ` is not absolutely convergent, and the conjugate
--   pairing of `Core.criticalZero_pair_inv` is genuinely responsible for convergence.
--
--   ```lean
--   theorem ReciprocalZeroHarmonics.not_summable_unpaired(b : ℝ) (g : ℕ → ℝ) (hpos : ∀ n, 0 < g n)
--       (hub : ∀ n : ℕ, g n ≤ b * ((n : ℝ) + 1)) : ¬ Summable fun n : ℕ => 1 / g n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ReciprocalZeroHarmonics/Convergence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ReciprocalZeroHarmonics/Convergence.lean#L213

-- Thm stub generated from Algebra/ReciprocalZeroHarmonics/Convergence.lean
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






/-! ## A quantitative truncation error -/



/-! ## Why the renormalisation is necessary -/

theorem ReciprocalZeroHarmonics.not_summable_unpaired(b : ℝ) (g : ℕ → ℝ) (hpos : ∀ n, 0 < g n)
    (hub : ∀ n : ℕ, g n ≤ b * ((n : ℝ) + 1)) : ¬ Summable fun n : ℕ => 1 / g n := by sorry
