-- Prove2me | Theorems.Thm_dvd_coeff_cycl_integer
-- name    : dvd_coeff_cycl_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:10.956288+00:00
-- url     : https://prove2.me/theorems/dbacacf2-bc4f-403a-91ed-3ba9b1ed7e0b
-- title:
--   dvd coeff cycl integer: dvd coeff cycl integer
-- statement:
--   The dvd coeff cycl integer construction uses the dvd coeff cycl integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L107-L153
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L107-L153

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
variable {L}

theorem dvd_coeff_cycl_integer (hp : p.Prime) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
    {f : Fin p → ℤ} (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : ↑m ∣ ∑ j, f j • ζ ^ (j : ℕ)) : ∀ j, m ∣ f j := by sorry
