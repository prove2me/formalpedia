-- Prove2me | Definitions.Def_Probability_PortfolioEpsInvisible
-- name    : Probability_PortfolioEpsInvisible
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:52.101886+00:00
-- url     : https://prove2.me/theorems/8e3db097-cb16-446e-83f6-9e192af2e101
-- title:
--   Aether Catalog definitions — Probability_PortfolioEpsInvisible
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioEpsInvisible`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioEpsInvisible.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Quantitative (ε-)invisibility: stability of the no-dial-edge theorem

`Probability.PortfolioRegretCore` proves that an *exactly* invisible observation
is worthless for scheduling: the optimal dial is the do-nothing dial.  Exact
invisibility is a knife-edge hypothesis, and no measurement can ever certify it.
This file replaces it by a measurable one.

An observation is **ε-invisible** for the portfolio when, on every fiber, the
(unnormalised) conditional cost of every member differs from its global
conditional mean `m s` by at most `ε` times the mass of the fiber:

`|fiberVal o s - fiberMass o * m s| ≤ ε * fiberMass o`.

Main results:

* `bestConstant_le_of_epsInvisible` — the best static member costs at most
  `min m + ε`;
* `dialValue_ge_of_epsInvisible` — the *optimal* observation-measurable rule
  costs at least `min m - ε`;
* `eps_invisible_gap_le` — hence `bestConstant - dialValue ≤ 2 * ε`: a small
  measured dial gain is a certificate of near-invisibility, and conversely
  near-invisibility caps the achievable gain.  This is the conjectured
  stability statement of the previous cycle (`FUTURE_DIRECTIONS.md`, direction 1);
* `eps_invisible_policy_ge` — the approximate no-dial-edge inequality for an
  arbitrary rule, degenerating to `no_dial_edge` at `ε = 0`;
* **sharpness**: the explicit "anti-diagonal" portfolios `spreadCost n`
  (`n+1` members, `n+1` fibers, uniform weights, cost `-1` on the diagonal and
  `+1` off it) are `1`-invisible with gap exactly `2 n / (n+1)`
  (`spread_gap`), so the constant `2` cannot be lowered
  (`eps_invisible_two_sharp`), while a *single* fiber pair already forces the gap
  to be at least `ε` (`spread_gap` at `n = 1`).

* **the naive converse fails** (`gap_zero_of_identical_members`,
  `gap_zero_not_epsInvisible`): a portfolio of indistinguishable members has dial
  gain `0` on *every* observation, and an explicit two-instance example with gain
  `0` fails to be `ε`-invisible for any `ε < 1` and any mean profile.  A null dial
  measurement is therefore one-sided evidence only.

Everything is finite and rational; no measure theory is involved.
-/

namespace Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## ε-invisibility -/

/-- **Quantitative invisibility.**  Relative to the observation `obs`, the
conditional cost of every member on every fiber agrees with the global mean
profile `m` up to a relative error `eps`. -/
def EpsInvisible [Fintype Ω] [DecidableEq O] (w : Ω → ℚ) (cost : Ω → S → ℚ)
    (obs : Ω → O) (m : S → ℚ) (eps : ℚ) : Prop :=
  ∀ (o : O) (s : S),
    |fiberVal w cost obs o s - fiberMass w obs o * m s| ≤ eps * fiberMass w obs o




/-! ## The two ends of the sandwich -/



/-! ## Stability of the no-dial-edge theorem -/




/-! ## Sharpness of the constant `2`

The "anti-diagonal" portfolio on `Fin (n+1)`: instance `o` is its own fiber, the
`o`-th member is the unique winner there (cost `-1`) and every other member pays
`+1`.  All members have the same global mean, so the portfolio is `1`-invisible,
yet an optimal dial saves `2 n / (n + 1)`. -/



/-- Uniform weights on `Fin (n+1)`. -/
def spreadW (n : ℕ) : Fin (n + 1) → ℚ := fun _ => 1 / (n + 1)

/-- Anti-diagonal cost matrix: member `s` wins exactly on instance `s`. -/
def spreadCost (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ℚ :=
  fun o s => if o = s then -1 else 1











/-! ## The naive converse fails

A zero dial gain does **not** certify `eps`-invisibility: if the members of the
portfolio are indistinguishable, no dial can gain anything however unbalanced the
fibers are. -/


/-- A two-instance portfolio with indistinguishable members. -/
def flatW : Fin 2 → ℚ := ![1/2, 1/2]

/-- Its cost matrix: `0` on the first instance, `2` on the second, for every
member. -/
def flatCost : Fin 2 → Fin 2 → ℚ := fun ω _ => if ω = 0 then 0 else 2



end Probability.PortfolioRegret


