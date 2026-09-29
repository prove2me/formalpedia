-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_mean_elimination_unsafe
-- name    : Probability.PortfolioRegret.mean_elimination_unsafe
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:03.363625+00:00
-- url     : https://prove2.me/theorems/4f48a19c-53fa-4004-80dc-59cfa66fe273
-- title:
--   Unsafe elimination.
-- statement:
--   **Unsafe elimination.**  Member `1` has twice the mean cost of member `0`,
--   yet it is the only member that is cheap on the tail: erasing it doubles the
--   expected oracle cost, from `1` to `2`.  Mean dominance is not an elimination
--   certificate.
--
--   ```lean
--   theorem Probability.PortfolioRegret.mean_elimination_unsafe:
--       (∀ i, 0 ≤ tailW i) ∧ (∑ i, tailW i = 1) ∧
--       EV tailW (fun ω => elimCost ω 0) = 2 ∧
--       EV tailW (fun ω => elimCost ω 1) = 4 ∧
--       EV tailW (oracleCost elimCost) = 1 ∧
--       EV tailW (oracleOn ((univ : Finset (Fin 2)).erase 1) ⟨0, by decide⟩ elimCost) = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioElimination.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioElimination.lean#L68

-- Thm stub generated from Probability/PortfolioElimination.lean
import Mathlib
import Definitions.Def_Probability_PortfolioElimination
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Eliminating a portfolio member: what is safe and what is not

Fourth cycle of the portfolio programme, formalising the ledger requirement that
*eliminations need dominance arguments, not mean comparisons*.

* `oracleOn` — the oracle restricted to a sub-portfolio.
* `oracleOn_erase_of_dominates` / `ev_oracleOn_erase_of_dominates` — **safe
  elimination**: a member that is dominated *pointwise* by another member may be
  deleted without changing the oracle, instancewise and in expectation.
* `mean_elimination_unsafe` — **unsafe elimination**: a member whose mean cost is
  twice that of another can nevertheless be the only member that keeps the oracle
  cheap; deleting it doubles the oracle's expected cost.  A mean comparison is
  therefore never sufficient grounds for elimination.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}

theorem Probability.PortfolioRegret.mean_elimination_unsafe:
    (∀ i, 0 ≤ tailW i) ∧ (∑ i, tailW i = 1) ∧
    EV tailW (fun ω => elimCost ω 0) = 2 ∧
    EV tailW (fun ω => elimCost ω 1) = 4 ∧
    EV tailW (oracleCost elimCost) = 1 ∧
    EV tailW (oracleOn ((univ : Finset (Fin 2)).erase 1) ⟨0, by decide⟩ elimCost) = 2 := by sorry
