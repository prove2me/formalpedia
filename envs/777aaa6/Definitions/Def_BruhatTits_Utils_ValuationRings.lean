-- Prove2me | Definitions.Def_BruhatTits_Utils_ValuationRings
-- name    : BruhatTits_Utils_ValuationRings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:42:30.877242+00:00
-- url     : https://prove2.me/theorems/b3f7764e-28d7-460d-880d-1c977e500899
-- title:
--   Valuation Rings
-- statement:
--   Definitions and structural lemmas for Valuation Rings, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
section
variable {K : Type*} [Field K] (R : Subring K)
@[simp]
lemma Subring.coe_zpow (a : Rˣ) (n : ℤ) :
    (a ^ n).val.val = a.val.val ^ n := by
  show (Units.map R.subtype (a ^ n) : Kˣ).val = (Units.map R.subtype a).val ^ n
  simp
end
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
lemma mem_subring_iff_integer (x : K) : x ∈ R ↔ v x ≤ 1 := by
  rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff, ← Set.mem_range]
  show x ∈ R ↔ x ∈ R.subtype.range
  rw [Subring.range_subtype]
omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma coe_inv_eq_inv_coe (u : Rˣ) : (u : K)⁻¹ = u⁻¹ := by
  field_simp
  simp only [← Subring.coe_mul]
  simp
lemma mem_or_inv_mem (x : K) : x ∈ R ∨ x⁻¹ ∈ R := by
  rw [mem_subring_iff_integer, mem_subring_iff_integer]
  by_cases h : v x ≤ 1
  · exact Or.inl h
  · apply Or.inr
    simp at h
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    rw [Valuation.one_lt_val_iff v hx] at h
    exact le_of_lt h
include hϖ in
lemma eq_unit_mul_pow_irreducible [IsDiscreteValuationRing R](x : K) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = u * ϖ ^ n := by
  cases mem_or_inv_mem (R := R) x
  · next h =>
    let x' : R := ⟨x, h⟩
    have hx' : x' ≠ 0 := Subtype.coe_ne_coe.mp hx
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    use n, u
    simpa using congrArg Subtype.val hu
  · next h =>
    let x' : R := ⟨x⁻¹, h⟩
    have hx' : x' ≠ 0 := (Subtype.coe_ne_coe).mp (inv_ne_zero hx)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    have : x = x'.val⁻¹ := by simp [x']
    use -n, u⁻¹
    rw [this, hu, mul_comm]
    ring_nf
    simp [inv_eq_iff_eq_inv, coe_inv_eq_inv_coe]
lemma eq_unit_mul_pow_irreducible' [IsDiscreteValuationRing R] (x : Kˣ) :
    ∃ (n : ℤ) (u : Rˣ), x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n := by
  have hx : x.val ≠ 0 := x.ne_zero
  obtain ⟨n, u, h⟩ := eq_unit_mul_pow_irreducible ϖ hϖ x.val hx
  use n, u
  ext
  rw [h]
  simp
variable [IsDiscreteValuationRing R]
noncomputable def zaddVal' (x : Kˣ) : ℤ :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose
noncomputable def zaddVal (x : Kˣ) : ℤ :=
  zaddVal'
    (IsDiscreteValuationRing.exists_irreducible R).choose
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec
    x


