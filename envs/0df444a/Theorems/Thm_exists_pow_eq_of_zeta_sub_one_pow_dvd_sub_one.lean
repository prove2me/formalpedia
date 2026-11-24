-- Prove2me | Theorems.Thm_exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one
-- name    : exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:05.127805+00:00
-- url     : https://prove2.me/theorems/71cafe5e-6528-4faa-803d-92f57e0ac009
-- title:
--   exists pow eq of zeta sub one pow dvd sub one: exists pow eq of zeta sub one pow dvd sub one
-- statement:
--   The exists pow eq of zeta sub one pow dvd sub one construction uses the exists pow eq of zeta sub one pow dvd sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L30-L52
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L30-L52

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

theorem exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one {u : (𝓞 K)ˣ}
    (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ p = u := by sorry
