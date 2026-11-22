-- Prove2me | Theorems.Thm_prod_eq
-- name    : prod_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:15.667362+00:00
-- url     : https://prove2.me/theorems/e882488c-7f52-4b6f-a753-eecc8af9e861
-- title:
--   prod eq: prod eq
-- statement:
--   The prod eq construction uses the prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Pair.lean#L27-L28
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Pair.lean#L27-L28

module
public import Mathlib.Util.Notation3
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
set_option autoImplicit true
@[expose] public section
public section
open scoped ZhangYeungPFR

theorem prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := by sorry

attribute [defeq] prod_eq
