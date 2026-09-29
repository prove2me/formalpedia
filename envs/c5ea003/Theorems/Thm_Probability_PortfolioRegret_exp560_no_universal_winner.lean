-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_exp560_no_universal_winner
-- name    : Probability.PortfolioRegret.exp560_no_universal_winner
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:57:11.759171+00:00
-- url     : https://prove2.me/theorems/2f0c3b14-020e-4dea-a545-37ece423a992
-- title:
--   No universal winner.
-- statement:
--   **No universal winner.**  Every member of the portfolio is strictly beaten by
--   the oracle on a set of positive mass, and every member wins on a set of positive
--   mass.
--
--   ```lean
--   theorem Probability.PortfolioRegret.exp560_no_universal_winner(s : Fin 5) :
--       (∃ x : Fin 5 × Fin 2, oracleCost exp560Cost x < exp560Cost x s) ∧
--       0 < ∑ x ∈ univ.filter (fun x : Fin 5 × Fin 2 => x.1 = s), exp560W x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioExp560.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioExp560.lean#L130

-- Thm stub generated from Probability/PortfolioExp560.lean
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The exp-560 portfolio: an exact rational model of the measured winner shares

A concrete instance of the theory of `Probability.PortfolioRegretCore`, built so
that its numbers coincide *exactly* with the measured ones of experiment 560:

| member (index)        | oracle winner share |
| --------------------- | ------------------- |
| `ρ` (Pollard rho, 0)  | `0.580`             |
| `p-1 @ 256` (1)       | `0.345`             |
| `PM1 @ 1024` (2)      | `0.045`             |
| Fermat (3)            | `0.028`             |
| trial division (4)    | `0.002`             |

The instance space is `Fin 5 × Fin 2`: the first coordinate is the *hidden*
`p-1` powersmoothness class (which member of the portfolio will win), the second
is an *observable* bit (a bit-length / balance quintile marker), drawn
independently of the class.  Every member costs `1` on the class it wins and the
common penalty `1179/140` elsewhere.

The verified consequences are:

* `exp560_winner_shares` — the oracle winner shares are exactly the table above;
* `exp560_no_universal_winner` — every member loses on a set of positive mass,
  so no member dominates the portfolio;
* `exp560_staticRegret` — the static regret against the oracle is exactly
  `3.117`, matching the measured value;
* `exp560_no_dial_edge` — *no* rule reading the observable bit beats the best
  static member: a tuned dial provably tunes itself to do-nothing;
* `exp560_ml_rule_strictly_worse` — the two-armed "learned" rule is strictly
  worse, with expected cost exactly `279385/56000 ≈ 4.989`;
* `exp560_probe_threshold` — a probe that reveals the hidden smoothness class is
  worth its price exactly when the price is below `3.117`.
-/

open Probability.PortfolioRegret

open Finset

/-! ## The model -/











/-! ## The oracle and the winner shares -/

theorem Probability.PortfolioRegret.exp560_no_universal_winner(s : Fin 5) :
    (∃ x : Fin 5 × Fin 2, oracleCost exp560Cost x < exp560Cost x s) ∧
    0 < ∑ x ∈ univ.filter (fun x : Fin 5 × Fin 2 => x.1 = s), exp560W x := by sorry
