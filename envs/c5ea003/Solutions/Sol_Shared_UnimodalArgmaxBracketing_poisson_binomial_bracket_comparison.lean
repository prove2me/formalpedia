-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.poisson_binomial_bracket_comparison
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:52:33.605314+00:00
-- url     : https://prove2.me/submissions/43b98738-12b0-435a-9e01-ef5833e775df

-- Sol generated from Shared/UnimodalArgmaxPoisson.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Definitions.Def_Shared_UnimodalArgmaxPoisson
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_brackets_mono
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_brackets_step
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_thresholdWindow
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



/-- **The Poisson rise criterion.**  The weights rise strictly at `k` iff `k+1 < lam`:
the threshold *is* the parameter. -/
theorem poissonWeight_lt_succ_iff (hlam : 0 < lam) (k : ℕ) :
    poissonWeight lam k < poissonWeight lam (k + 1) ↔ ((k : ℝ) + 1) < lam := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hfs : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp : (0 : ℝ) < lam ^ k := pow_pos hlam k
  have key : (poissonWeight lam k < poissonWeight lam (k + 1)) ↔
      (((k : ℝ) + 1) * lam ^ k < lam * lam ^ k) := by
    unfold poissonWeight
    rw [hfs, pow_succ, div_lt_div_iff₀ hf (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [key, mul_lt_mul_iff_of_pos_right hp]

/-- The weak Poisson rise criterion. -/
theorem poissonWeight_le_succ_iff (hlam : 0 < lam) (k : ℕ) :
    poissonWeight lam k ≤ poissonWeight lam (k + 1) ↔ ((k : ℝ) + 1) ≤ lam := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hfs : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp : (0 : ℝ) < lam ^ k := pow_pos hlam k
  have key : (poissonWeight lam k ≤ poissonWeight lam (k + 1)) ↔
      (((k : ℝ) + 1) * lam ^ k ≤ lam * lam ^ k) := by
    unfold poissonWeight
    rw [hfs, pow_succ, div_le_div_iff₀ hf (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [key, mul_le_mul_iff_of_pos_right hp]

/-- The Poisson weights form a threshold window with threshold `lam`, as soon as the
window `[0, n]` is long enough to contain the peak. -/
theorem poissonWeight_thresholdWindow (hlam : 0 < lam) (hn : lam < (n : ℝ) + 1) :
    ThresholdWindow n (poissonWeight lam) lam :=
  ⟨hlam, hn, fun k _ => poissonWeight_lt_succ_iff hlam k,
    fun k _ => poissonWeight_le_succ_iff hlam k⟩





/-! ## Binomial versus Poisson: the two bracketing degrees differ by at most one -/

/-- With `p = lam / n` and `q = 1 - lam / n` the binomial mode parameter is
`lam + lam / n`. -/
theorem modeParameter_of_poisson_scaling (hlam : 0 < lam) (hn : lam < (n : ℝ)) :
    modeParameter n (lam / (n : ℝ)) (1 - lam / (n : ℝ)) = lam + lam / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hlam hn
  have hsum : lam / (n : ℝ) + (1 - lam / (n : ℝ)) = 1 := by ring
  rw [modeParameter, hsum, div_one]
  field_simp



open Shared in
theorem solution(hlam : 0 < lam) (hn : lam < (n : ℝ)) :
    lastArgmax n (poissonWeight lam)
        ≤ lastArgmax n (binomialWeight n (lam / (n : ℝ)) (1 - lam / (n : ℝ))) ∧
      lastArgmax n (binomialWeight n (lam / (n : ℝ)) (1 - lam / (n : ℝ)))
        ≤ lastArgmax n (poissonWeight lam) + 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hlam hn
  have hp : (0 : ℝ) < lam / (n : ℝ) := by positivity
  have hq : (0 : ℝ) < 1 - lam / (n : ℝ) := by
    have : lam / (n : ℝ) < 1 := (div_lt_one hnpos).2 hn
    linarith
  have hratio : lam / (n : ℝ) < 1 := (div_lt_one hnpos).2 hn
  have hPois : ThresholdWindow n (poissonWeight lam) lam :=
    poissonWeight_thresholdWindow hlam (by linarith)
  have hBin : ThresholdWindow n (binomialWeight n (lam / (n : ℝ)) (1 - lam / (n : ℝ)))
      (lam + lam / (n : ℝ)) := by
    have := binomialWeight_thresholdWindow (n := n) hp hq
    rwa [modeParameter_of_poisson_scaling hlam hn] at this
  refine ⟨(ThresholdWindow.brackets_mono hPois hBin (by linarith [hp])).2,
    (ThresholdWindow.brackets_step hPois hBin (by linarith)).2⟩
