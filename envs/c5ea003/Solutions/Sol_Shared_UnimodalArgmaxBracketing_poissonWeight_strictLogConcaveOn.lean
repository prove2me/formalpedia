-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.poissonWeight_strictLogConcaveOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:52:33.108158+00:00
-- url     : https://prove2.me/submissions/ae1d8826-83f5-4a97-ba28-45762d354e8a

-- Sol generated from Shared/UnimodalArgmaxPoisson.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Definitions.Def_Shared_UnimodalArgmaxPoisson
/-
# The Poisson window, and the comparison of *binomial* versus *Poisson* brackets

Third cycle on top of `Shared.UnimodalArgmaxBracketing` (abstract theory of the two
bracketing degrees) and `Shared.UnimodalArgmaxBinomial` (the binomial instance).

The Poisson weights `poissonWeight lam k = lam ^ k / k!` form a strictly log-concave
window on `[0, n]`, and they are a **threshold window with threshold exactly `lam`**:
the rise criterion is the strikingly simple `k + 1 < lam`.  Consequently the two
bracketing degrees are `⌈lam⌉₊ - 1` and `⌊lam⌋₊`, and the explicit comparison of the
two degrees is: *the gap is `1` iff `lam` is a positive integer* — the classical
"Poisson mode is `⌊lam⌋`, with a tie at `lam - 1` for integral `lam`".

The final result is a genuine **cross-instance comparison**: for the binomial window
with success weight `p = lam / n` (so that the expected number of successes is
`lam`), the two bracketing degrees of the *binomial* window and those of the
*Poisson* window differ by at most one, in a completely explicit way
(`poisson_binomial_bracket_comparison`).  Both statements are instances of the same
abstract lemma `ThresholdWindow.brackets_step`, applied to two thresholds that differ
by less than one (`lam` versus `lam + lam / n`).
-/

open Shared
open UnimodalArgmaxBracketing

/-! ## The Poisson weights -/


variable {lam : ℝ} {n : ℕ}

theorem poissonWeight_pos (hlam : 0 < lam) (k : ℕ) : 0 < poissonWeight lam k := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  unfold poissonWeight
  positivity









/-! ## Binomial versus Poisson: the two bracketing degrees differ by at most one -/




open Shared in
theorem solution(hlam : 0 < lam) :
    StrictLogConcaveOn n (poissonWeight lam) := by
  refine ⟨fun k _ => poissonWeight_pos hlam k, fun k _ => ?_⟩
  have hfactNat : ((k + 1).factorial) ^ 2 < k.factorial * (k + 2).factorial := by
    have h1 : (k + 1).factorial = (k + 1) * k.factorial := rfl
    have h2 : (k + 2).factorial = (k + 2) * ((k + 1) * k.factorial) := rfl
    rw [h1, h2]
    have hk : 0 < k.factorial := k.factorial_pos
    nlinarith [hk]
  have hfact : ((k + 1).factorial : ℝ) ^ 2 < (k.factorial : ℝ) * ((k + 2).factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hfk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hfk1 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
  have hfk2 : (0 : ℝ) < ((k + 2).factorial : ℝ) := by exact_mod_cast (k + 2).factorial_pos
  unfold poissonWeight
  rw [div_mul_div_comm, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hpow : lam ^ k * lam ^ (k + 2) = (lam ^ (k + 1)) ^ 2 := by ring
  rw [hpow]
  exact mul_lt_mul_of_pos_left hfact (by positivity)
