-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialPerturbation_rho_swap_exact
-- name    : Catalog.Novelty.ZeroFitDialPerturbation.rho_swap_exact
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:19:20.324755+00:00
-- url     : https://prove2.me/theorems/c6a3ac53-0d55-4f97-ab69-352dbc24bfe8
-- title:
--   The corresponding exact change in `ρ`: one extreme transposition moves the
-- statement:
--   The corresponding exact change in `ρ`: one extreme transposition moves the
--   coefficient by `12(n-1)/(n(n+1))`, i.e. `Θ(1/n)`, matching the Lipschitz law's rate.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialPerturbation.rho_swap_exact{n : ℕ} (hn : 2 ≤ n) (R S S' : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
--       (hi : S' i = S j) (hj : S' j = S i) (hrest : ∀ k, k ≠ i → k ≠ j → S k = S' k)
--       (hRi : R i = 1) (hRj : R j = (n : ℚ)) (hSi : S i = 1) (hSj : S j = (n : ℚ)) :
--       rhoRank R S - rhoRank R S' = 12 * ((n : ℚ) - 1) / ((n : ℚ) * ((n : ℚ) + 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialPerturbation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialPerturbation.lean#L198

-- Thm stub generated from Novelty/ZeroFitDialPerturbation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialPerturbation
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

open Catalog.Novelty.ZeroFitDialPerturbation





/-! ## 1. Localisation and the per-coordinate bound -/




/-! ## 2. The rank-perturbation Lipschitz law -/



/-! ## 3. The budget law -/



/-! ## 4. Sharpness: the exact transposition increment -/

theorem Catalog.Novelty.ZeroFitDialPerturbation.rho_swap_exact{n : ℕ} (hn : 2 ≤ n) (R S S' : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
    (hi : S' i = S j) (hj : S' j = S i) (hrest : ∀ k, k ≠ i → k ≠ j → S k = S' k)
    (hRi : R i = 1) (hRj : R j = (n : ℚ)) (hSi : S i = 1) (hSj : S j = (n : ℚ)) :
    rhoRank R S - rhoRank R S' = 12 * ((n : ℚ) - 1) / ((n : ℚ) * ((n : ℚ) + 1)) := by sorry
