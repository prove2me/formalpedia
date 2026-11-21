-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_free_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:21.074295+00:00
-- url     : https://prove2.me/submissions/ff56f715-b65c-400a-b3cb-a681903e3e1a

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
import Theorems.Thm_Kourovka_CentralLattice_le_saturation
import Theorems.Thm_Kourovka_CentralLattice_exists_retraction
import Theorems.Thm_Kourovka_CentralLattice_map_mem_saturation

set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
namespace Kourovka.CentralLattice
theorem _root_.solution [Module.Finite ℤ M] [NoZeroSMulDivisors ℤ M]
    (c : Z →ₗ[ℤ] M) (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ x ∈ saturation (LinearMap.range c), d • x ∈ (LinearMap.range c))
    (hu : ∀ x ∈ (LinearMap.range c), u x ∈ (LinearMap.range c))
    (hrow : ∀ y, ∃ x z, u x + c z = y)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  let S := saturation (LinearMap.range c)
  obtain ⟨p, hp⟩ := exists_retraction (LinearMap.range c)
  have hdelta : ∀ x : S, x.val - u x.val ∈ (LinearMap.range c) := by
    intro x
    obtain ⟨y, hy⟩ := hcong x.val
    have hs : u x.val - x.val ∈ S :=
      S.sub_mem (map_mem_saturation (LinearMap.range c) u hu x.property) x.property
    rw [hy] at hs
    have hsy : y ∈ S := (smul_mem_saturation_iff (LinearMap.range c) hd y).mp hs
    have hdy := hden y hsy
    have hneg := (LinearMap.range c).neg_mem hdy
    simpa only [← hy, neg_sub] using hneg
  let delta : S →ₗ[ℤ] (LinearMap.range c) :=
    (S.subtype - u.comp S.subtype).codRestrict (LinearMap.range c) hdelta
  obtain ⟨k, hk⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict c) delta
    (by rintro ⟨x, z, rfl⟩; exact ⟨z, rfl⟩)
  let h := k.comp p
  refine ⟨h, ?_⟩
  let v := u + c.comp h
  have hv : ∀ x : S, v x.val = x.val := by
    intro x
    have he := congrArg (fun f : S →ₗ[ℤ] (LinearMap.range c) => (f x).val) hk
    change c (k x) = x.val - u x.val at he
    change u x.val + c (k (p x.val)) = x.val
    rw [hp x, he]
    abel
  have hdiff : ∀ x, v x - u x ∈ S := by
    intro x
    change (u x + c (h x)) - u x ∈ S
    have hc : c (h x) ∈ S := le_saturation (LinearMap.range c) ⟨h x, rfl⟩
    simpa only [add_sub_cancel_left] using hc
  intro y
  obtain ⟨x, z, hz⟩ := hrow y
  have hsy : y - v x ∈ S := by
    rw [← hz]
    have hc : c z ∈ S := le_saturation (LinearMap.range c) ⟨z, rfl⟩
    have he : u x + c z - v x = c z - (v x - u x) := by abel
    rw [he]
    exact S.sub_mem hc (hdiff x)
  refine ⟨x + (y - v x), ?_⟩
  change v (x + (y - v x)) = y
  rw [map_add, hv ⟨y - v x, hsy⟩]
  simp [sub_eq_add_neg, add_left_comm]
end Kourovka.CentralLattice
