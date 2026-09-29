-- Prove2me | Theorems.Thm_CircuitComplexity_MCircuit_card_vars_le_size
-- name    : CircuitComplexity.MCircuit.card_vars_le_size
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:42.544834+00:00
-- url     : https://prove2.me/theorems/51af2b45-6c64-4c2e-a399-1928aa6cd741
-- title:
--   The number of distinct variables in a circuit is at most its size.
-- statement:
--   The number of distinct variables in a circuit is at most its size.
--
--   ```lean
--   theorem CircuitComplexity.MCircuit.card_vars_le_size[DecidableEq ι] (C : MCircuit ι) : C.vars.card ≤ C.size := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/BasicMonotoneCircuit/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/BasicMonotoneCircuit/Basic.lean#L78

-- Thm stub generated from Logic/BasicMonotoneCircuit/Basic.lean
import Mathlib
import Definitions.Def_Logic_BasicMonotoneCircuit_Basic

/-! # Basic monotone circuit complexity -/

open CircuitComplexity


open MCircuit

variable {ι : Type*}

theorem CircuitComplexity.MCircuit.card_vars_le_size[DecidableEq ι] (C : MCircuit ι) : C.vars.card ≤ C.size := by sorry
