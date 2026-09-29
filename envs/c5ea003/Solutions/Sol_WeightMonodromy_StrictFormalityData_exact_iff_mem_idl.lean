-- Prove2me | solution 1 for WeightMonodromy.StrictFormalityData.exact_iff_mem_idl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:35:35.780799+00:00
-- url     : https://prove2.me/submissions/1063d193-3779-4f6e-ab6c-8a727e585163

import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality

open WeightMonodromy in
theorem solution {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] {D : WeightedDGA 𝒜}
    (F : StrictFormalityData D) (z : A) (hz : z ∈ F.sub) (hdz : D.d z = 0) :
    (∃ c : A, z = D.d c) ↔ z ∈ F.idl := by
  constructor
  · -- a sub-cocycle bounding in `A` bounds in `sub`, and `d` maps `sub` into `idl`
    rintro ⟨c, hc⟩
    obtain ⟨c', hc', hzc'⟩ := F.qis_inj z hz c hc
    rw [hzc']
    exact F.d_sub c' hc'
  · -- the ideal is acyclic
    intro hzi
    obtain ⟨j', -, hj'⟩ := F.idl_acyclic z hzi hdz
    exact ⟨j', hj'⟩
