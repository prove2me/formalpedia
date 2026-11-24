-- Prove2me | Theorems.Thm_systemOfUnits_ex_not_mem
-- name    : systemOfUnits.ex_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:10.208801+00:00
-- url     : https://prove2.me/theorems/8f6f7367-8229-4f75-9976-bdd756abdd67
-- title:
--   system Of Units: ex not mem
-- statement:
--   The system Of Units construction uses the ex not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L46-L55

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
variable [Module (CyclotomicIntegers p) G]
open systemOfUnits
include hp
include hf
set_option backward.isDefEq.respectTransparency false

theorem systemOfUnits.ex_not_mem [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by sorry
