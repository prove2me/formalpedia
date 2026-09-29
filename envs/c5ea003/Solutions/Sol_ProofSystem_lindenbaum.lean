-- Prove2me | solution 1 for ProofSystem.lindenbaum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:13:10.361636+00:00
-- url     : https://prove2.me/submissions/394cf144-9650-4ce0-8cd8-61466a6b2bcd

import Mathlib
import Definitions.Def_Novelty_UniversalMathematicsLindenbaum

open Set ProofSystem in
theorem solution {S : Type*} (P : ProofSystem S) {base : Set S} (hcon : P.Consistent base) :
    ∃ M, base ⊆ M ∧ P.Consistent M ∧ P.C M = M ∧
      ∀ Δ, M ⊆ Δ → P.Consistent Δ → Δ = M := by
  -- consistent extensions of `base`, ordered by inclusion
  let F : Set (Set S) := {Γ | base ⊆ Γ ∧ P.Consistent Γ}
  -- chains have consistent unions, by compactness
  have hchain : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s, hs⟩ := hne
      exact (hcF hs).1.trans (Set.subset_sUnion_of_mem hs)
    · show P.bot ∉ P.C (⋃₀ c)
      intro hbot
      obtain ⟨Γ₀, hsub, hfin, hΓ₀⟩ := P.compact hbot
      obtain ⟨t, htc, hst⟩ :=
        hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hfin hsub
      exact (hcF htc).2 (P.mono hst hΓ₀)
  obtain ⟨M, hbM, hmax⟩ := zorn_subset_nonempty F hchain base ⟨subset_rfl, hcon⟩
  have hMF : M ∈ F := hmax.prop
  have hmaxeq : ∀ Δ ∈ F, M ⊆ Δ → Δ = M := fun Δ hΔ hMΔ => (hmax.eq_of_le hΔ hMΔ).symm
  refine ⟨M, hbM, hMF.2, ?_, fun Δ hMΔ hΔ => hmaxeq Δ ⟨hbM.trans hMΔ, hΔ⟩ hMΔ⟩
  -- the deductive closure of a maximal consistent theory is still consistent
  exact hmaxeq (P.C M) ⟨hbM.trans (P.subset_closure M), fun h => hMF.2 (P.idem M h)⟩
    (P.subset_closure M)
