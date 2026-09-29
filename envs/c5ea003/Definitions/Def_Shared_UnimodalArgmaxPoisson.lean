-- Prove2me | Definitions.Def_Shared_UnimodalArgmaxPoisson
-- name    : Shared_UnimodalArgmaxPoisson
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:16:46.231843+00:00
-- url     : https://prove2.me/theorems/1a034381-1043-4939-8df8-2983b0d953a7
-- title:
--   Aether Catalog definitions — Shared_UnimodalArgmaxPoisson
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.UnimodalArgmaxPoisson`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/UnimodalArgmaxPoisson.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
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

namespace Shared
namespace UnimodalArgmaxBracketing

/-! ## The Poisson weights -/

/-- The (unnormalised) Poisson weight `lam ^ k / k!`. -/
noncomputable def poissonWeight (lam : ℝ) (k : ℕ) : ℝ := lam ^ k / (Nat.factorial k : ℝ)

variable {lam : ℝ} {n : ℕ}










/-! ## Binomial versus Poisson: the two bracketing degrees differ by at most one -/



end UnimodalArgmaxBracketing
end Shared


