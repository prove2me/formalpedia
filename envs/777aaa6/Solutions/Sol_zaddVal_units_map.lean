-- Prove2me | solution 1 for zaddVal_units_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:06:07.685751+00:00
-- url     : https://prove2.me/submissions/40c45885-547b-406c-b388-0bbe592ed790

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_zaddVal_eq_iff__c79a38cac4fc
import Theorems.Thm_zaddVal_mul
attribute [local simp] zaddVal_mul

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (x : Rˣ) :
    zaddVal (R := R) (Units.map R.subtype x) = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [zaddVal_eq_iff' ϖ hϖ]
  use x
  simp
