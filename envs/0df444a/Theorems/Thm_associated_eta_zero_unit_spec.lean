-- Prove2me | Theorems.Thm_associated_eta_zero_unit_spec
-- name    : associated_eta_zero_unit_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:24.411704+00:00
-- url     : https://prove2.me/theorems/ecd101a9-e479-499b-9994-266ce71e9385
-- title:
--   associated eta zero unit spec: associated eta zero unit spec
-- statement:
--   The associated eta zero unit spec construction uses the associated eta zero unit spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/InductionStep.lean#L488-L491
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/InductionStep.lean#L488-L491

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.ClassGroup.Basic
public import Definitions.Def_FltRegular_CaseII_AuxLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
public import Definitions.Def_FltRegular_CaseII_InductionStep
set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
local notation3 "π" => hζ.toInteger - 1
local notation3 "𝔭" => Ideal.span {π}
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}
local notation3 "𝔵" => Ideal.span {x}
local notation3 "𝔶" => Ideal.span {y}
local notation3 "𝔷" => Ideal.span {z}
variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
variable (η : nthRootsFinset p (1 : 𝓞 K))
local notation3 "𝔪" => gcd 𝔵 𝔶
variable [hpri : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]
local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η
local notation "𝔷'" => zDivM hζ e hy
local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy
local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy
local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy
variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg
local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg

theorem associated_eta_zero_unit_spec (η) (hη : η ≠ η₀) :
    ε η hη * (x + y * η₀) * α η hη ^ p = (x + y * η) * π ^ (m * p) * β η hη ^ p := by sorry
