-- Prove2me | Definitions.Def_Probability_PortfolioExp560
-- name    : Probability_PortfolioExp560
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:53.833497+00:00
-- url     : https://prove2.me/theorems/3284b0b1-5c21-4c3e-8fcb-8da895b9e54c
-- title:
--   Aether Catalog definitions — Probability_PortfolioExp560
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioExp560`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioExp560.lean by skeleton subtraction
import Mathlib
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

namespace Probability.PortfolioRegret

open Finset

/-! ## The model -/

/-- Masses of the five hidden powersmoothness classes: `0.580, 0.345, 0.045,
`0.028`, `0.002`. -/
def classW : Fin 5 → ℚ
  | 0 => 58/100
  | 1 => 69/200
  | 2 => 9/200
  | 3 => 7/250
  | 4 => 1/500

/-- The observable bit is a fair coin, independent of the hidden class. -/
def obsW : Fin 2 → ℚ
  | 0 => 1/2
  | 1 => 1/2

/-- Product weights on `Fin 5 × Fin 2`. -/
def exp560W : Fin 5 × Fin 2 → ℚ := fun x => classW x.1 * obsW x.2

/-- The common penalty paid by a member off its own class. -/
def penalty : ℚ := 1179/140

/-- Cost matrix: a member costs `1` on its class and `penalty` elsewhere. -/
def exp560Cost : Fin 5 × Fin 2 → Fin 5 → ℚ := fun x s => if s = x.1 then 1 else penalty

/-- The observation available to a scheduler: the `N`-visible bit only. -/
def exp560Obs : Fin 5 × Fin 2 → Fin 2 := Prod.snd

/-- Conditional mean cost of each member — the same on both fibers. -/
def exp560Mean : Fin 5 → ℚ := fun s => classW s + (1 - classW s) * penalty




/-! ## The oracle and the winner shares -/





/-! ## Invisibility of the observable bit -/







/-! ## Static value, regret, and the impotence of every dial -/








end Probability.PortfolioRegret


