-- Prove2me | Theorems.Thm_ZhangYeung_IdentDistrib_condMutualInfo_eq
-- name    : ZhangYeung.IdentDistrib.condMutualInfo_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:10:01.995722+00:00
-- url     : https://prove2.me/theorems/aa4e891c-ea16-478a-b3a4-1ce008d04cb2
-- title:
--   Ident Distrib: cond Mutual Info eq
-- statement:
--   Substituting variables for identically-distributed ones leaves the conditional mutual
--   information
--   unchanged. PFR exposes `IdentDistrib.condEntropy_eq` and `IdentDistrib.mutualInfo_eq`
--   but not this
--   conditional-mutual-information transport. The three sub-`IdentDistrib`s for `⟨X, Z⟩`,
--   `⟨Y, Z⟩`, and
--   `⟨⟨X, Y⟩, Z⟩` are extracted from the triple by one `IdentDistrib.comp` with a measurable
--   projection
--   each. Promoted from `ZhangYeung/CopyLemma.lean` as of M5.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L42-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L42-L75

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung

theorem ZhangYeung.IdentDistrib.condMutualInfo_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S T U : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    [Finite S] [Finite T] [Finite U]
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
                      (fun ω' => (X' ω', Y' ω', Z' ω')) μ μ') :
    I[X : Y | Z; μ] = I[X' : Y' | Z'; μ'] := by sorry
