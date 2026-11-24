-- Prove2me | Theorems.Thm_fltIdeals_coprime
-- name    : fltIdeals_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:01.729051+00:00
-- url     : https://prove2.me/theorems/398cd114-1961-4c44-8ccf-5f926aa05f46
-- title:
--   flt Ideals coprime: flt Ideals coprime
-- statement:
--   The flt Ideals coprime construction uses the flt Ideals coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L89-L103

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

theorem fltIdeals_coprime (hpri : p.Prime) (p5 : 5 ≤ p) {x y z : ℤ}
    (H : x ^ p + y ^ p = z ^ p) {η₁ η₂ : R} (hxy : IsCoprime x y)
    (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1)
    (hdiff : η₁ ≠ η₂)
    (caseI : ¬↑p ∣ x * y * z) :
    have : Fact p.Prime := ⟨hpri⟩
    IsCoprime (fltIdeals p x y hη₁) (fltIdeals p x y hη₂) := by sorry
