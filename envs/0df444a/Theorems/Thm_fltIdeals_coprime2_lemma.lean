-- Prove2me | Theorems.Thm_fltIdeals_coprime2_lemma
-- name    : fltIdeals_coprime2_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:54.844233+00:00
-- url     : https://prove2.me/theorems/1a3b6155-e80c-40fd-a903-02ead1237939
-- title:
--   flt Ideals coprime2 lemma: flt Ideals coprime2 lemma
-- statement:
--   The flt Ideals coprime2 lemma construction uses the flt Ideals coprime2 lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L57-L79

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

theorem fltIdeals_coprime2_lemma [Fact p.Prime] (ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p 1)
    (hη₂ : η₂ ∈ nthRootsFinset p 1) (hdiff : η₁ ≠ η₂) (hp : IsCoprime x y)
    (hp2 : ¬(p : ℤ) ∣ (x + y : ℤ)) (hwlog : η₁ ≠ 1) :
    (fltIdeals p x y hη₁) ⊔ (fltIdeals p x y hη₂) = ⊤ := by sorry
