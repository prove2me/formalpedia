-- Prove2me | Theorems.Thm_diff_of_roots
-- name    : diff_of_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:51.865885+00:00
-- url     : https://prove2.me/theorems/f3ce410e-d728-444f-86b4-f0b559f11e23
-- title:
--   diff of roots: diff of roots
-- statement:
--   The diff of roots construction uses the diff of roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L47-L55

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

theorem diff_of_roots [hp : Fact p.Prime] (ph : 5 ≤ p) {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1)
    (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
    ∃ u : Rˣ, η₁ - η₂ = u * (1 - η₁) := by sorry
