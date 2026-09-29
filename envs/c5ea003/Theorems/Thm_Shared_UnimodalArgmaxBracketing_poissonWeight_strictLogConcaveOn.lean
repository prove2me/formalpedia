-- Prove2me | Theorems.Thm_Shared_UnimodalArgmaxBracketing_poissonWeight_strictLogConcaveOn
-- name    : Shared.UnimodalArgmaxBracketing.poissonWeight_strictLogConcaveOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:46.497372+00:00
-- url     : https://prove2.me/theorems/ae3ba53f-928a-4a42-8768-1db5df5079ad
-- title:
--   Strict log-concavity of the Poisson weights, from `(k+1)!Â² < k!
-- statement:
--   Strict log-concavity of the Poisson weights, from `(k+1)!Â² < k! (k+2)!`.
--
--   ```lean
--   theorem Shared.UnimodalArgmaxBracketing.poissonWeight_strictLogConcaveOn(hlam : 0 < lam) :
--       StrictLogConcaveOn n (poissonWeight lam) := by sorry
--
--
--
--
--
--
--
--   /-! ## Binomial versus Poisson: the two bracketing degrees differ by at most one -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/UnimodalArgmaxPoisson.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/UnimodalArgmaxPoisson.lean#L40

-- Thm stub generated from Shared/UnimodalArgmaxPoisson.lean
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

theorem Shared.UnimodalArgmaxBracketing.poissonWeight_strictLogConcaveOn(hlam : 0 < lam) :
    StrictLogConcaveOn n (poissonWeight lam) := by sorry
