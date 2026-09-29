-- Prove2me | solution 1 for CircuitComplexity.MCircuit.card_vars_le_size
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:50.379241+00:00
-- url     : https://prove2.me/submissions/91c82d77-f17b-4ba8-8d31-a24e69ccae48

-- Sol generated from Logic/BasicMonotoneCircuit/Basic.lean
import Mathlib
import Definitions.Def_Logic_BasicMonotoneCircuit_Basic

/-! # Basic monotone circuit complexity -/

open CircuitComplexity


open MCircuit

variable {ι : Type*}











open CircuitComplexity.MCircuit in
theorem solution[DecidableEq ι] (C : MCircuit ι) : C.vars.card ≤ C.size := by
  induction C with
  | var i => simp [vars, size]
  | top => simp [vars, size]
  | bot => simp [vars, size]
  | and a b iha ihb =>
      simp only [vars, size]
      calc
        (a.vars ∪ b.vars).card ≤ a.vars.card + b.vars.card := Finset.card_union_le _ _
        _ ≤ a.size + b.size := Nat.add_le_add iha ihb
        _ ≤ a.size + b.size + 1 := Nat.le_succ _
  | or a b iha ihb =>
      simp only [vars, size]
      calc
        (a.vars ∪ b.vars).card ≤ a.vars.card + b.vars.card := Finset.card_union_le _ _
        _ ≤ a.size + b.size := Nat.add_le_add iha ihb
        _ ≤ a.size + b.size + 1 := Nat.le_succ _
