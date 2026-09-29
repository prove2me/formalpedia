-- Prove2me | solution 1 for SimpleGraph.IsStarSum.isIndepSet_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T06:08:08.66441+00:00
-- url     : https://prove2.me/submissions/6e1013c1-3dd2-465f-8f8a-27c5ccea4d93

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

open SimpleGraph

open SimpleGraph in
/-- **Independent sets of the parts that all contain the centre glue to an independent set.** -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [DecidableEq V] [Fintype ι] {s : ι → Finset V}
    (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i)) (hv : ∀ i, v ∈ s i) :
    G.IsIndepSet ↑(Finset.univ.biUnion s) := by
  classical
  have htr : ∀ x ∈ Finset.univ.biUnion s, ∀ k, x ∈ A k → x ∈ s k := by
    intro x hx k hxk
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, -, hxi⟩ := hx
    by_cases hxv : x = v
    · rw [hxv]; exact hv k
    · by_cases hik : i = k
      · exact hik ▸ hxi
      · exfalso
        have hm : x ∈ A i ∩ A k := ⟨hs i hxi, hxk⟩
        rw [h.inter_eq i k hik] at hm
        exact hxv hm
  intro x hx y hy hxy hG
  rw [h.sup_eq, SimpleGraph.iSup_adj] at hG
  obtain ⟨k, hk⟩ := hG
  exact hi k (htr x hx k (h.support k hk).1) (htr y hy k (h.support k hk).2) hxy hk
