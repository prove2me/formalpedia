-- Prove2me | Theorems.Thm_P2M_zaddVal_eq_iff__c79a38cac4fc
-- name    : P2M_zaddVal_eq_iff__c79a38cac4fc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:06.114014+00:00
-- url     : https://prove2.me/theorems/c149bd15-2575-41f6-87f1-be019b595a71
-- title:
--   P2 M zadd Val eq iff  c79a38cac4fc: P2 M zadd Val eq iff  c79a38cac4fc
-- statement:
--   The P2 M zadd Val eq iff  c79a38cac4fc construction uses the P2 M zadd Val eq iff  c79a38cac4fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L311-L314
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L311-L314

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ

theorem P2M_zaddVal_eq_iff__c79a38cac4fc (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), u * ϖ.val ^ n = x := by sorry

alias «zaddVal_eq_iff'» := P2M_zaddVal_eq_iff__c79a38cac4fc
