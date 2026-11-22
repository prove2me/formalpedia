-- Prove2me | solution 1 for P2M_zaddVal_eq_iff__c79a38cac4fc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:48.801624+00:00
-- url     : https://prove2.me/submissions/df66ae77-d3f4-4eb8-95fa-9b8cb31c9cf9

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_zaddVal_eq_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
theorem _root_.solution (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), u * ϖ.val ^ n = x := by
  rw [zaddVal_eq_iff ϖ hϖ]
  simp [Units.ext_iff]
