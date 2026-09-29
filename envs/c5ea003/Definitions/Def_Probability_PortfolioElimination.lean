-- Prove2me | Definitions.Def_Probability_PortfolioElimination
-- name    : Probability_PortfolioElimination
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:45.409634+00:00
-- url     : https://prove2.me/theorems/8a78dc4d-6f0f-470c-bedf-e6a4489c4669
-- title:
--   Aether Catalog definitions — Probability_PortfolioElimination
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioElimination`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioElimination.lean by skeleton subtraction
import Mathlib
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}

/-- The oracle restricted to the sub-portfolio `T`. -/
noncomputable def oracleOn (T : Finset S) (hT : T.Nonempty) (cost : Ω → S → ℚ) (ω : Ω) : ℚ :=
  T.inf' hT (cost ω)



/-- The two-member portfolio witnessing the failure of mean-based elimination:
member `0` is cheap on the bulk, member `1` is cheap exactly on the tail. -/
def elimCost : Fin 2 → Fin 2 → ℚ := ![![1, 5], ![5, 1]]



end Probability.PortfolioRegret


