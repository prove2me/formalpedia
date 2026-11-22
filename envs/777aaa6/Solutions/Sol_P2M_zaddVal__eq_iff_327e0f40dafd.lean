-- Prove2me | solution 1 for P2M_zaddVal__eq_iff_327e0f40dafd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:31.582805+00:00
-- url     : https://prove2.me/submissions/7d3d1f7a-4aa4-4361-8ba4-406e7deb6d9a

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_zaddVal__spec_8ebf7135ac48
import Theorems.Thm_unit_mul_zpow_congr_zpow

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (n : ℤ) (x : Kˣ) :
    zaddVal' (R := R) ϖ hϖ x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by
  constructor
  · intro h
    rw [← h]
    use (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec.choose
    exact (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec.choose_spec.symm
  · rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := zaddVal'_spec ϖ hϖ x
    nth_rw 1 [← hu] at hy
    rw [Units.ext_iff] at hy
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      Units.val_zpow_eq_zpow_val, Units.val_mk0] at hy
    apply unit_mul_zpow_congr_zpow hϖ hϖ y u
    exact hy.symm
