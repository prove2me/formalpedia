-- Prove2me | Theorems.Thm_aux_lem_flt
-- name    : aux_lem_flt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:41.167821+00:00
-- url     : https://prove2.me/theorems/fd379cd7-f191-494c-b0d0-05c05f5a903b
-- title:
--   aux lem flt: aux lem flt
-- statement:
--   The aux lem flt construction uses the aux lem flt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L37-L45

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional Polynomial Algebra Nat Finset Fintype
variable (p : ℕ) (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
open scoped NumberField
open Ideal IsCyclotomicExtension
local notation "R" => 𝓞 (CyclotomicField p ℚ)
variable {p}
open IsPrimitiveRoot

theorem aux_lem_flt [Fact p.Prime] {x y z : ℤ} (H : x ^ p + y ^ p = z ^ p)
    (caseI : ¬↑p ∣ x * y * z) : ¬(p : ℤ) ∣ (x + y : ℤ) := by sorry
