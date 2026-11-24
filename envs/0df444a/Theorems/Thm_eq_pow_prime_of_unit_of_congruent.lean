-- Prove2me | Theorems.Thm_eq_pow_prime_of_unit_of_congruent
-- name    : eq_pow_prime_of_unit_of_congruent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:12.924007+00:00
-- url     : https://prove2.me/theorems/5c46a715-d876-42d0-a1e4-b34d4bec885a
-- title:
--   eq pow prime of unit of congruent: eq pow prime of unit of congruent
-- statement:
--   A regular prime criterion: if a unit of the cyclotomic field is congruent to an integer
--   modulo `p`, then it is a `p`-th power.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L56-L102
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L56-L102

module
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
set_option autoImplicit false
@[expose] public section
public section
open Polynomial IsCyclotomicExtension.Rat
open scoped NumberField
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)
include hp hreg

theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) :
    ∃ v, u = v ^ p := by sorry
