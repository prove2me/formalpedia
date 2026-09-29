-- Prove2me | Definitions.Def_Probability_PortfolioDialEdge
-- name    : Probability_PortfolioDialEdge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:35.516991+00:00
-- url     : https://prove2.me/theorems/f8476e83-70bf-4a3b-97b9-b9ea1fcbff03
-- title:
--   Aether Catalog definitions — Probability_PortfolioDialEdge
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioDialEdge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioDialEdge.lean by skeleton subtraction
import Mathlib
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω O O' S : Type*}

/-- Unnormalised conditional cost of member `s` on the fiber of `obs` over `o`. -/
def fiberVal [Fintype Ω] [DecidableEq O] (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O)
    (o : O) (s : S) : ℚ :=
  ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω s

/-- The value of the *optimal* rule measurable with respect to `obs`. -/
noncomputable def dialValue [Fintype Ω] [Fintype O] [DecidableEq O] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) : ℚ :=
  ∑ o, univ.inf' univ_nonempty (fiberVal w cost obs o)











end Probability.PortfolioRegret


