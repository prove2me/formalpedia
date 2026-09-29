-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_dialValue_le_bestConstant
-- name    : Probability.PortfolioRegret.dialValue_le_bestConstant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:32.200441+00:00
-- url     : https://prove2.me/theorems/b6d98dc9-b16b-4130-ac8d-dc60281d420b
-- title:
--   An optimised dial never costs more than the best static member.
-- statement:
--   An optimised dial never costs more than the best static member.
--
--   ```lean
--   theorem Probability.PortfolioRegret.dialValue_le_bestConstant[Fintype Ω] [Fintype O] [DecidableEq O]
--       [Fintype S] [Nonempty S] (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) :
--       dialValue w cost obs ≤ bestConstant w cost := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioDialEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioDialEdge.lean#L86

-- Thm stub generated from Probability/PortfolioDialEdge.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# When does a dial help?  An exact characterisation, and the information ladder

Second cycle of the portfolio programme.  `Probability.PortfolioRegretCore`
shows that an *invisible* observation gives no scheduling edge.  Here we drop the
invisibility hypothesis entirely and compute the exact optimum over all
observation-measurable rules.

For an observation map `obs` write `fiberVal o s` for the unnormalised
conditional cost of member `s` on the fiber over `o`.  Then

* `ev_policy_eq_sum_fiberVal` — every rule costs `∑ o, fiberVal o (π o)`;
* `dialValue` `= ∑ o, min_s fiberVal o s` is attained (`exists_optimal_dial`)
  and is a lower bound for every rule (`dialValue_le_ev_policy`);
* `dialValue_le_bestConstant` — a dial never hurts if it is *optimised*;
* `dial_edge_iff` — **exact characterisation**: an optimised dial strictly beats
  the best static member if and only if every member is beaten on some fiber;
* `dialValue_mono_of_refines` — a finer observation is worth (weakly) more:
  monotonicity of the value of information;
* `ev_oracle_le_dialValue` — the whole ladder
  `E[oracle] ≤ dialValue ≤ bestConstant`.

Combined with the `N`-invisibility of the `p - 1` powersmoothness channel
(`Probability.PortfolioSmoothnessChannel`), `dial_edge_iff` explains the measured
`Δ = 0.000`: the tuned dial found nothing because on each fiber the same member
minimises the conditional cost.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O O' S : Type*}

theorem Probability.PortfolioRegret.dialValue_le_bestConstant[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [Nonempty S] (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) :
    dialValue w cost obs ≤ bestConstant w cost := by sorry
