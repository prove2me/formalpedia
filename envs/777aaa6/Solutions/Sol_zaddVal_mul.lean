-- Prove2me | solution 1 for zaddVal_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:04:29.644386+00:00
-- url     : https://prove2.me/submissions/770861e4-1cbb-4053-b7a9-637e700ad15b

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_zaddVal_eq_iff__c79a38cac4fc
import Theorems.Thm_eq_unit_mul_zpow_zaddVal

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (x y : Kˣ) :
    zaddVal (R := R) (x * y) = zaddVal (R := R) x + zaddVal (R := R) y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ux, hux⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ x
  obtain ⟨uy, huy⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ y
  rw [zaddVal_eq_iff' ϖ hϖ]
  use ux * uy
  simp only [Units.val_mul, Subring.coe_mul]
  rw [zpow_add₀, ← hux, ← huy]
  ring
  repeat simpa using hϖ.ne_zero
