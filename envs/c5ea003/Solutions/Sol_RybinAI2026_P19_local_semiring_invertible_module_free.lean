-- Prove2me | solution 1 for RybinAI2026.P19.local_semiring_invertible_module_free
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:34:59.798706+00:00
-- url     : https://prove2.me/submissions/216cd13d-f461-4af3-8679-1d6460925510

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

open scoped TensorProduct BigOperators

theorem solution (R M : Type*) [CommSemiring R] [IsLocalRing R]
    [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    Module.Free R M := by
  classical
  obtain ⟨z,hz⟩ := (Module.Invertible.bijective (R := R) (M := M)).surjective 1
  obtain ⟨s,rfl⟩ := TensorProduct.exists_finset z
  have hs : IsUnit (∑ a ∈ s, a.1 a.2) := by
    have heq : (∑ a ∈ s, a.1 a.2) = 1 := by
      simpa only [map_sum,contractLeft_apply] using hz
    rw [heq]
    exact isUnit_one
  have hsum (s : Finset (Module.Dual R M × M)) (f : (Module.Dual R M × M) → R) :
      IsUnit (∑ i ∈ s, f i) → ∃ i ∈ s, IsUnit (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.sum_insert has]
      intro h
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with ha | hrest
      · exact ⟨a,Finset.mem_insert_self _ _,ha⟩
      · obtain ⟨i,hi,hfi⟩ := ih hrest
        exact ⟨i,Finset.mem_insert_of_mem hi,hfi⟩
  obtain ⟨⟨f,m⟩,_,u,hu⟩ := hsum s (fun a : Module.Dual R M × M => a.1 a.2) hs
  have hf : Function.Surjective f := by
    intro r
    refine ⟨(r * ↑u⁻¹) • m,?_⟩
    simp only [map_smul,smul_eq_mul,← hu]
    simp [mul_assoc]
  exact Module.Invertible.free_iff_linearEquiv.mpr
    ⟨LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hf)⟩
