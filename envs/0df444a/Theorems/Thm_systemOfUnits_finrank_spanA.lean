-- Prove2me | Theorems.Thm_systemOfUnits_finrank_spanA
-- name    : systemOfUnits.finrank_spanA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:25.828473+00:00
-- url     : https://prove2.me/theorems/055c5722-39c7-41b9-b1f9-ff2509e59aeb
-- title:
--   system Of Units: finrank span A
-- statement:
--   The system Of Units construction uses the finrank span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L35-L41

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

theorem systemOfUnits.finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by sorry
