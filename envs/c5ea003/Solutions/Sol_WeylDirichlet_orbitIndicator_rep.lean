-- Prove2me | solution 1 for WeylDirichlet.orbitIndicator_rep
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:33:23.19753+00:00
-- url     : https://prove2.me/submissions/1a8ecd30-5b59-414f-ac06-7e6a6690c7d2

import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan
import Definitions.Def_Geometry_WeylDirichletDecomposition_OrbitBasis
open Classical WeylDirichlet MulAction in
theorem solution {G X ι R : Type*} [Group G] [MulAction G X] [Semiring R] (rep : ι → X)
    (hunique : ∀ x, ∃! i, x ∈ MulAction.orbit G (rep i)) (i j : ι) :
    (orbitIndicator G rep i (rep j) : R) = if i = j then 1 else 0 := by
  -- `rep j` lies in the orbit of `rep i` exactly when `i = j`
  have hmem : rep j ∈ MulAction.orbit G (rep i) ↔ i = j := by
    constructor
    · intro h
      obtain ⟨k, -, hk⟩ := hunique (rep j)
      exact (hk i h).trans (hk j (MulAction.mem_orbit_self (rep j))).symm
    · rintro rfl
      exact MulAction.mem_orbit_self (rep i)
  unfold orbitIndicator
  by_cases h : i = j
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]
