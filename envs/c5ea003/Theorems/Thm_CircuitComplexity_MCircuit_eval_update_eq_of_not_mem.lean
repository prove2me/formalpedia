-- Prove2me | Theorems.Thm_CircuitComplexity_MCircuit_eval_update_eq_of_not_mem
-- name    : CircuitComplexity.MCircuit.eval_update_eq_of_not_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:42.159951+00:00
-- url     : https://prove2.me/theorems/c729a269-965a-4543-878c-171bd0bc9b5a
-- title:
--   Updating a variable absent from a circuit cannot change its evaluation.
-- statement:
--   Updating a variable absent from a circuit cannot change its evaluation.
--
--   ```lean
--   theorem CircuitComplexity.MCircuit.eval_update_eq_of_not_mem[DecidableEq ι] (C : MCircuit ι) (x : ι → Bool)
--       {i : ι} (hi : i ∉ C.vars) (b : Bool) : C.eval (Function.update x i b) = C.eval x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/BasicMonotoneCircuit/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/BasicMonotoneCircuit/Basic.lean#L54

-- Thm stub generated from Logic/BasicMonotoneCircuit/Basic.lean
import Mathlib
import Definitions.Def_Logic_BasicMonotoneCircuit_Basic

/-! # Basic monotone circuit complexity -/

open CircuitComplexity


open MCircuit

variable {ι : Type*}

theorem CircuitComplexity.MCircuit.eval_update_eq_of_not_mem[DecidableEq ι] (C : MCircuit ι) (x : ι → Bool)
    {i : ι} (hi : i ∉ C.vars) (b : Bool) : C.eval (Function.update x i b) = C.eval x := by sorry
