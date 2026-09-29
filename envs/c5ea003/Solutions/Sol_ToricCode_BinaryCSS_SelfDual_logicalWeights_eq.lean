-- Prove2me | solution 1 for ToricCode.BinaryCSS.SelfDual.logicalWeights_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:48:18.936974+00:00
-- url     : https://prove2.me/submissions/012ce3f0-e67e-41e0-b380-74daaaa868e4

import Mathlib
import Definitions.Def_Geometry_ToricCode_Dual
import Definitions.Def_Geometry_ToricCode_SelfDuality

open ToricCode Matrix

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [DecidableEq E]
variable {C : BinaryCSS V E F}

private theorem hammingNorm_comp_equiv (z : E → F2) (τ : E ≃ E) :
    hammingNorm (z ∘ τ) = hammingNorm z := by
  classical
  simp only [hammingNorm]
  refine Finset.card_equiv τ ?_
  intro e; simp [Function.comp]

private theorem cycles_comp_tau (S : BinaryCSS.SelfDual C) (z : E → F2) :
    z ∈ C.cycles ↔ z ∘ S.tau ∈ C.dualCycles := by
  simp only [BinaryCSS.cycles, BinaryCSS.dualCycles, LinearMap.mem_ker]
  constructor
  · intro hz
    change C.A *ᵥ z = 0 at hz
    have h := S.intertwine_cycle z
    show C.Bᵀ *ᵥ (z ∘ S.tau) = 0
    rw [h, hz, Pi.zero_comp]
  · intro hz
    change C.Bᵀ *ᵥ (z ∘ S.tau) = 0 at hz
    have h := S.intertwine_cycle z
    have hAzσ : (C.A *ᵥ z) ∘ S.sigma = 0 := by rw [← h, hz]
    show C.A *ᵥ z = 0
    funext v
    obtain ⟨f, hf⟩ := S.sigma.surjective v
    have := congr_fun hAzσ f
    simp only [Function.comp, Pi.zero_apply] at this
    simpa [hf] using this

private theorem comp_tau_inj (τ : E ≃ E) {f g : E → F2} (h : f ∘ τ = g ∘ τ) : f = g := by
  funext e
  simpa using congr_fun h (τ.symm e)

private theorem boundaries_comp_tau (S : BinaryCSS.SelfDual C) (z : E → F2) :
    z ∈ C.boundaries ↔ z ∘ S.tau ∈ C.dualBoundaries := by
  simp only [BinaryCSS.boundaries, BinaryCSS.dualBoundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g ∘ S.rho, (S.intertwine_boundary g).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h ∘ S.rho.symm, ?_⟩
    have hint := S.intertwine_boundary (h ∘ S.rho.symm)
    have hcomp :
        (C.B *ᵥ (h ∘ S.rho.symm)) ∘ S.tau = z ∘ S.tau := by
      calc
        (C.B *ᵥ (h ∘ S.rho.symm)) ∘ S.tau
            = C.Aᵀ *ᵥ ((h ∘ S.rho.symm) ∘ S.rho) := hint
        _   = C.Aᵀ *ᵥ h := by simp [Function.comp_assoc]
        _   = z ∘ S.tau := hh
    exact comp_tau_inj S.tau hcomp

theorem solution (S : BinaryCSS.SelfDual C) :
    C.dualLogicalWeights = C.logicalWeights := by
  ext w
  simp only [BinaryCSS.logicalWeights, BinaryCSS.dualLogicalWeights, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hzC, hzB, rfl⟩
    refine ⟨z ∘ S.tau.symm, ?_, ?_, hammingNorm_comp_equiv z S.tau.symm⟩
    · have hzC' : (z ∘ S.tau.symm) ∘ S.tau ∈ C.dualCycles := by
        simpa [Function.comp_assoc] using hzC
      exact (cycles_comp_tau S (z ∘ S.tau.symm)).mpr hzC'
    · intro hb
      have : (z ∘ S.tau.symm) ∘ S.tau ∈ C.dualBoundaries :=
        (boundaries_comp_tau S (z ∘ S.tau.symm)).mp hb
      have : z ∈ C.dualBoundaries := by simpa [Function.comp_assoc] using this
      exact hzB this
  · rintro ⟨z, hzC, hzB, rfl⟩
    refine ⟨z ∘ S.tau, (cycles_comp_tau S z).mp hzC, ?_,
      hammingNorm_comp_equiv z S.tau⟩
    intro hb
    exact hzB ((boundaries_comp_tau S z).mpr hb)
