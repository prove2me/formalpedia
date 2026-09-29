-- Prove2me | solution 1 for WeylDirichlet.invariant_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:53:19.867716+00:00
-- url     : https://prove2.me/submissions/bcdbe588-df85-468d-bfb3-f9aa0dd0a256

import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan
import Definitions.Def_Geometry_WeylDirichletDecomposition_OrbitBasis
open Classical WeylDirichlet MulAction in
theorem solution {G X ι R : Type*} [Group G] [MulAction G X] [Semiring R] [Fintype ι] (rep : ι → X)
    (hunique : ∀ x, ∃! i, x ∈ MulAction.orbit G (rep i))
    (f : X → R) (hinv : ∀ (g : G) (x : X), f (g • x) = f x) (x : X) :
    f x = ∑ i, f (rep i) * orbitIndicator G rep i x := by
  -- exactly one orbit contains `x`, and `f` is constant on it
  obtain ⟨i₀, hi₀, huniq⟩ := hunique x
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hi₀
  rw [Finset.sum_eq_single i₀]
  · unfold orbitIndicator
    rw [if_pos hi₀, mul_one, ← hg, hinv]
  · intro j _ hj
    unfold orbitIndicator
    rw [if_neg (fun h => hj (huniq j h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
