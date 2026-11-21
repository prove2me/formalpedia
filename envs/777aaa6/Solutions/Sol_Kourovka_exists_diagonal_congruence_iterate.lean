-- Prove2me | solution 1 for Kourovka.exists_diagonal_congruence_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:30.643183+00:00
-- url     : https://prove2.me/submissions/ab6fd0bd-8a2c-49ee-9b74-de980dc2de95

import Definitions.Def_Kourovka_CentralLattice
import Definitions.Def_Kourovka_CentralPeriod
import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DiagonalCongruence
import Theorems.Thm_Kourovka_abelianMap_iterate_of
import Theorems.Thm_Kourovka_CentralPeriod_exists_iterate_congr
import Theorems.Thm_Kourovka_abelianization_map_surjective


set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (dA dB : ℤ) (hdA : dA ≠ 0) (hdB : dB ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      (∀ x : Additive (Abelianization A), ∃ y,
        CentralLattice.abelianMap (diagonalLeft (ProductPaths.iterateHom f n)) x - x = dA • y) ∧
      (∀ x : Additive (Abelianization B), ∃ y,
        CentralLattice.abelianMap (diagonalRight (ProductPaths.iterateHom f n)) x - x = dB • y) := by
  let M := Additive (Abelianization (A × B))
  have hfab : Function.Surjective (CentralLattice.abelianMap f) := abelianization_map_surjective f hf
  obtain ⟨n, hn, hcong⟩ := CentralPeriod.exists_iterate_congr M
    (CentralLattice.abelianMap f) hfab (dA * dB) (mul_ne_zero hdA hdB)
  refine ⟨n, hn, ?_, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    let p : M →ₗ[ℤ] Additive (Abelianization A) :=
      (Abelianization.map (MonoidHom.fst A B)).toAdditive.toIntLinearMap
    obtain ⟨y, hy⟩ := hcong (Additive.ofMul (Abelianization.of (a, (1 : B))))
    have hp := congrArg p hy
    rw [map_sub, map_smul, abelianMap_iterate_of] at hp
    change CentralLattice.abelianMap (diagonalLeft (ProductPaths.iterateHom f n))
      (Additive.ofMul (Abelianization.of a)) - Additive.ofMul (Abelianization.of a) =
        (dA * dB) • p y at hp
    refine ⟨dB • p y, ?_⟩
    rw [← mul_smul]
    exact hp
  · intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    let p : M →ₗ[ℤ] Additive (Abelianization B) :=
      (Abelianization.map (MonoidHom.snd A B)).toAdditive.toIntLinearMap
    obtain ⟨y, hy⟩ := hcong (Additive.ofMul (Abelianization.of ((1 : A), b)))
    have hp := congrArg p hy
    rw [map_sub, map_smul, abelianMap_iterate_of] at hp
    change CentralLattice.abelianMap (diagonalRight (ProductPaths.iterateHom f n))
      (Additive.ofMul (Abelianization.of b)) - Additive.ofMul (Abelianization.of b) =
        (dA * dB) • p y at hp
    refine ⟨dA • p y, ?_⟩
    rw [← mul_smul, mul_comm dB dA]
    exact hp
end Kourovka
