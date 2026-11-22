-- Prove2me | solution 1 for eq_unit_mul_zpow_zaddVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:39.818522+00:00
-- url     : https://prove2.me/submissions/a9138308-27b2-42b7-bb4a-54bdc853f6a1

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_zaddVal_eq_iff__c79a38cac4fc

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
theorem _root_.solution (x : Kˣ) :
    ∃ (u : Rˣ), u * ϖ.val ^ zaddVal (R := R) x = x :=
  (zaddVal_eq_iff' ϖ hϖ (zaddVal (R := R) x) x).mp rfl
