-- Prove2me | Definitions.Def_Kourovka_CentralLattice
-- name    : Kourovka_CentralLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:29:12.74618+00:00
-- url     : https://prove2.me/theorems/1945342d-1bb0-44c2-a35e-f82da8f4d60c
-- title:
--   Central Lattice
-- statement:
--   Definitions and structural lemmas for Central Lattice, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
namespace Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
def saturation (D : Submodule ℤ M) : Submodule ℤ M :=
  (Submodule.torsion ℤ (M ⧸ D)).comap D.mkQ
theorem mem_saturation (D : Submodule ℤ M) (x : M) :
    x ∈ saturation D ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ D := by
  change (∃ n : ℤ⁰, n • D.mkQ x = 0) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, nonZeroDivisors.coe_ne_zero n, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero D).mp hn
  · rintro ⟨n, hn, hx⟩
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩,
      (Submodule.Quotient.mk_eq_zero D).mpr hx⟩
theorem smul_mem_saturation_iff (D : Submodule ℤ M) {n : ℤ} (hn : n ≠ 0) (x : M) :
    n • x ∈ saturation D ↔ x ∈ saturation D := by
  constructor
  · intro hx
    obtain ⟨m, hm, hmx⟩ := (mem_saturation D _).mp hx
    exact (mem_saturation D x).mpr ⟨m * n, mul_ne_zero hm hn, by
      simpa only [mul_smul] using hmx⟩
  · exact (saturation D).smul_mem n
instance quotientSaturation_torsionFree (D : Submodule ℤ M) :
    NoZeroSMulDivisors ℤ (M ⧸ saturation D) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intro n x h
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      obtain ⟨x, rfl⟩ := (saturation D).mkQ_surjective x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      apply (smul_mem_saturation_iff D hn x).mp
      exact (Submodule.Quotient.mk_eq_zero _).mp h
theorem map_torsion (u : M →ₗ[ℤ] M) {x : M}
    (hx : x ∈ Submodule.torsion ℤ M) : u x ∈ Submodule.torsion ℤ M := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  change (n : ℤ) • u x = 0
  change (n : ℤ) • x = 0 at hn
  simpa only [map_smul, map_zero] using congrArg u hn
abbrev FreeQuotient (M : Type*) [AddCommGroup M] := M ⧸ Submodule.torsion ℤ M
def freeMap (u : M →ₗ[ℤ] M) : FreeQuotient M →ₗ[ℤ] FreeQuotient M :=
  (Submodule.torsion ℤ M).mapQ (Submodule.torsion ℤ M) u (fun _ => map_torsion u)
@[simp] theorem freeMap_mkQ (u : M →ₗ[ℤ] M) (x : M) :
    freeMap u ((Submodule.torsion ℤ M).mkQ x) =
      (Submodule.torsion ℤ M).mkQ (u x) := rfl
section Groups
variable {G : Type*} [Group G]
def abelianMap (u : G →* G) :
    Additive (Abelianization G) →ₗ[ℤ] Additive (Abelianization G) :=
  (Abelianization.map u).toAdditive.toIntLinearMap
def centerImage : Additive (Subgroup.center G) →ₗ[ℤ] Additive (Abelianization G) :=
  (Abelianization.of.comp (Subgroup.center G).subtype).toAdditive.toIntLinearMap
def centralLift
    (k : Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G)) :
    G →* Subgroup.center G where
  toFun x := Additive.toMul (k (Additive.ofMul (Abelianization.of x)))
  map_one' := by
    change k (Additive.ofMul (Abelianization.of 1)) = 0
    simpa only [map_one] using k.map_zero
  map_mul' x y := by
    change k (Additive.ofMul (Abelianization.of (x * y))) =
      k (Additive.ofMul (Abelianization.of x)) + k (Additive.ofMul (Abelianization.of y))
    rw [map_mul]
    exact k.map_add _ _
end Groups
end Kourovka.CentralLattice


