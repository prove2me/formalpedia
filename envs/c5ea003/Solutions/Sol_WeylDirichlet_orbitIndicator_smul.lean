-- Prove2me | solution 1 for WeylDirichlet.orbitIndicator_smul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:28:57.137167+00:00
-- url     : https://prove2.me/submissions/5faf2bc6-f13c-4cd5-bd93-616af8e2aec2

import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan
import Definitions.Def_Geometry_WeylDirichletDecomposition_OrbitBasis
open WeylDirichlet in
theorem solution {G X ι R : Type*} [Group G] [MulAction G X] [Semiring R]
    (rep : ι → X) (i : ι) (g : G) (x : X) :
    (orbitIndicator G rep i (g • x) : R) = orbitIndicator G rep i x := by
  unfold orbitIndicator
  -- orbits are `G`-stable, so `g • x` and `x` lie in the same orbits
  have h : g • x ∈ MulAction.orbit G (rep i) ↔ x ∈ MulAction.orbit G (rep i) := by
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨g⁻¹ * h, by simp only at hh ⊢; rw [mul_smul, hh, inv_smul_smul]⟩
    · rintro ⟨h, hh⟩
      exact ⟨g * h, by simp only at hh ⊢; rw [mul_smul, hh]⟩
  by_cases hx : x ∈ MulAction.orbit G (rep i)
  · rw [if_pos (h.mpr hx), if_pos hx]
  · rw [if_neg (fun h' => hx (h.mp h')), if_neg hx]
