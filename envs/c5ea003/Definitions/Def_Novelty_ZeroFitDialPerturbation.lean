-- Prove2me | Definitions.Def_Novelty_ZeroFitDialPerturbation
-- name    : Novelty_ZeroFitDialPerturbation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:56:04.284113+00:00
-- url     : https://prove2.me/theorems/47c86e32-aa21-430e-ae1b-3b8226e920d2
-- title:
--   Aether Catalog definitions — Novelty_ZeroFitDialPerturbation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ZeroFitDialPerturbation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ZeroFitDialPerturbation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76

/-!
# The corruption budget: how much re-ranking a dial move costs

Cycle 2 of the round-65 (bitlen-76) investigation.

`Novelty.ZeroFitDialU76` proves that the *tie geometry* of the zero-count statistic
is flat: between bitlen 72 and bitlen 76 the attainable Spearman ceiling moves by
less than `10^{-43}`, and between bitlen 64 and 76 by less than `10^{-30}` times the
recorded drop `0.648 → 0.608`.  So whatever moves the dial is not tie granularity —
it must act on the *ranks themselves*.

This file quantifies that alternative.  Working with raw rank vectors
`R, S : Fin n → ℚ` and the Spearman coefficient in `d²` form
`ρ = 1 - 6·Σᵢ(Rᵢ-Sᵢ)²/(n³-n)`, we prove:

* `sumSqD_sub_eq` — localisation: if `S` and `S'` agree off a set `A`, the `Σd²`
  difference is supported on `A`;
* `abs_sumSqD_sub_le` — each disagreeing coordinate can move `Σd²` by at most
  `(n-1)²`, hence `|Σd²(R,S) - Σd²(R,S')| ≤ |A|(n-1)²`;
* `abs_rho_sub_le` and `abs_rho_sub_le_div` — the **rank-perturbation Lipschitz law**
  `|ρ(R,S) - ρ(R,S')| ≤ 6|A|(n-1)/(n(n+1)) ≤ 6|A|/n`;
* `corruption_budget` — the contrapositive **budget law**: a dial move of size `δ`
  requires at least `δn/6` re-ranked observations;
* `u76_corruption_budget` — applied to the recorded `0.648 → 0.608` drop: at least
  `n/150` of the sample (0.67%) must be re-ranked;
* `sumSqD_swap_exact` and `rho_swap_exact` — sharpness: a single transposition
  changes `Σd²` by *exactly* `-2(Rᵢ-Rⱼ)(Sᵢ-Sⱼ)`, and transposing the two extreme
  ranks realises the per-coordinate bound `(n-1)²` exactly, so the Lipschitz law
  above is tight up to the constant 2.

Nothing here assumes the ranks come from any particular statistic: the bound holds
for *every* mechanism acting by re-ranking, which is what makes it a budget.
-/

open Finset

namespace Catalog.Novelty.ZeroFitDialPerturbation


/-- The Spearman `Σd²` statistic of two rank vectors. -/
def sumSqD {n : ℕ} (R S : Fin n → ℚ) : ℚ := ∑ i, (R i - S i) ^ 2

/-- Spearman's rank correlation in `d²` form. -/
def rhoRank {n : ℕ} (R S : Fin n → ℚ) : ℚ := 1 - 6 * sumSqD R S / ((n : ℚ) ^ 3 - n)

/-- `R` is a rank vector: all its entries lie in `[1, n]`. -/
def IsRankVec (n : ℕ) (R : Fin n → ℚ) : Prop := ∀ i, 1 ≤ R i ∧ R i ≤ (n : ℚ)

/-! ## 1. Localisation and the per-coordinate bound -/




/-! ## 2. The rank-perturbation Lipschitz law -/



/-! ## 3. The budget law -/



/-! ## 4. Sharpness: the exact transposition increment -/




end Catalog.Novelty.ZeroFitDialPerturbation


