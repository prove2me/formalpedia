-- Prove2me | solution 1 for CircuitComplexity.MCircuit.eval_update_eq_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:51.300884+00:00
-- url     : https://prove2.me/submissions/bfc21b52-41f5-4100-b681-25211d9f2d10

-- Sol generated from Logic/BasicMonotoneCircuit/Basic.lean
import Mathlib
import Definitions.Def_Logic_BasicMonotoneCircuit_Basic

/-! # Basic monotone circuit complexity -/

open CircuitComplexity


open MCircuit

variable {ι : Type*}











open CircuitComplexity.MCircuit in
theorem solution[DecidableEq ι] (C : MCircuit ι) (x : ι → Bool)
    {i : ι} (hi : i ∉ C.vars) (b : Bool) : C.eval (Function.update x i b) = C.eval x := by
  induction C with
  | var j =>
      simp only [vars, Finset.mem_singleton] at hi
      simp [eval, Function.update, Ne.symm hi]
  | top => rfl
  | bot => rfl
  | and a c iha ihc =>
      simp only [vars, Finset.mem_union, not_or] at hi
      simp only [eval, iha hi.1, ihc hi.2]
  | or a c iha ihc =>
      simp only [vars, Finset.mem_union, not_or] at hi
      simp only [eval, iha hi.1, ihc hi.2]
