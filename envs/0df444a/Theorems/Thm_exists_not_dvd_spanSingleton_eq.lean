-- Prove2me | Theorems.Thm_exists_not_dvd_spanSingleton_eq
-- name    : exists_not_dvd_spanSingleton_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:31.025899+00:00
-- url     : https://prove2.me/theorems/b124c761-e59b-4778-a5a9-a34824767f7d
-- title:
--   exists not dvd span Singleton eq: exists not dvd span Singleton eq
-- statement:
--   The exists not dvd span Singleton eq construction uses the exists not dvd span Singleton eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/AuxLemmas.lean#L14-L75
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/AuxLemmas.lean#L14-L75

module
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Definitions.Def_FltRegular_CaseII_AuxLemmas
set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}
open scoped nonZeroDivisors
open Polynomial
open FractionalIdeal

theorem exists_not_dvd_spanSingleton_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : Prime x) (I J : Ideal R)
    (hI : ¬ (Ideal.span <| singleton x) ∣ I) (hJ : ¬ (Ideal.span <| singleton x) ∣ J)
    (h : Submodule.IsPrincipal ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) : ∃ a b : R,
    ¬(x ∣ a) ∧ ¬(x ∣ b) ∧
      spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by sorry
