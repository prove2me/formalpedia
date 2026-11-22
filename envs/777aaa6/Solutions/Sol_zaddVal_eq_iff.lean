-- Prove2me | solution 1 for zaddVal_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:17.411808+00:00
-- url     : https://prove2.me/submissions/a7f461b3-c291-4383-b5a5-a35049965e3c

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_zaddVal_spec
import Theorems.Thm_unit_mul_zpow_congr_zpow

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by
  constructor
  · intro h
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    rw [h] at hy
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hp
    use y * a ^ n
    ext
    simp [hy, mul_zpow]
    group
  · rintro ⟨u, hu⟩
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    nth_rw 1 [← hu] at hy
    rw [Units.ext_iff] at hy
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      Units.val_zpow_eq_zpow_val, Units.val_mk0] at hy
    apply unit_mul_zpow_congr_zpow hp hϖ y u
    exact hy.symm
