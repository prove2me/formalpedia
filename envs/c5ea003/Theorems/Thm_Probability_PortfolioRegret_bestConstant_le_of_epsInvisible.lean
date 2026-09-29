-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_bestConstant_le_of_epsInvisible
-- name    : Probability.PortfolioRegret.bestConstant_le_of_epsInvisible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:24.196501+00:00
-- url     : https://prove2.me/theorems/6893d696-5717-461e-96da-6bdaaaac413d
-- title:
--   Under `eps`-invisibility the best static member costs at most `min m + eps`.
-- statement:
--   Under `eps`-invisibility the best static member costs at most `min m + eps`.
--
--   ```lean
--   theorem Probability.PortfolioRegret.bestConstant_le_of_epsInvisible[Fintype Ω] [Fintype O] [DecidableEq O]
--       [Fintype S] [Nonempty S]
--       {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ} {eps : ℚ}
--       (hw : ∑ ω, w ω = 1) (h : EpsInvisible w cost obs m eps) :
--       bestConstant w cost ≤ univ.inf' univ_nonempty m + eps := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioEpsInvisible.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioEpsInvisible.lean#L88

-- Thm stub generated from Probability/PortfolioEpsInvisible.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
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

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## ε-invisibility -/





/-! ## The two ends of the sandwich -/

theorem Probability.PortfolioRegret.bestConstant_le_of_epsInvisible[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [Nonempty S]
    {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ} {eps : ℚ}
    (hw : ∑ ω, w ω = 1) (h : EpsInvisible w cost obs m eps) :
    bestConstant w cost ≤ univ.inf' univ_nonempty m + eps := by sorry
