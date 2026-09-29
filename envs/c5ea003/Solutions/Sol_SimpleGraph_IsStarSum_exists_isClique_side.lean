-- Prove2me | solution 1 for SimpleGraph.IsStarSum.exists_isClique_side
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:00:36.100227+00:00
-- url     : https://prove2.me/submissions/7e5ea7b1-c39a-4d83-b403-2dc7a859cad6

/-
# `SimpleGraph.IsStarSum.exists_isClique_side`
Target `6d19cc02` (CE x4 — no published signature). Gift: SAFE.

BINDERS: DERIVED, not transcribed. `[Nonempty ι]` is load-bearing — with `ι` empty there is no index
to exhibit, even for `s = ∅`. `h` is a leading positional argument (`include h` at bundle line 76,
confirmed by the sibling b996f45a's WA). The type-match gate confirms or corrects this.

MATHS. `IsClique s = s.Pairwise G.Adj` (Clique.lean:47).
* `s` subsingleton: `h.union_eq` puts its point in some side; `IsClique.of_subsingleton` finishes.
* otherwise pick distinct `x y ∈ s`. They are adjacent, so `iSup_adj` + `h.support` put BOTH in one
  side `A k`. Being distinct, at least one of them — call it `p` — is `≠ v`. For any `z ∈ s`, the
  edge `z–p` lies in some `A k'`; if `k' ≠ k` then `p ∈ A k ∩ A k' = {v}`, contradicting `p ≠ v`.
  So `k' = k`, giving `s ⊆ A k`, and the same argument puts every edge of `s` inside `H k`.
-/
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

set_option maxHeartbeats 800000

open SimpleGraph Finset

open SimpleGraph in
/-- **The target, verbatim.** -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : G.IsStarSum H A v) [Nonempty ι] {s : Set V} (hs : G.IsClique s) :
    ∃ i, s ⊆ A i ∧ (H i).IsClique s := by
  have cut : ∀ {x : V} {i j : ι}, i ≠ j → x ∈ A i → x ∈ A j → x = v := by
    intro x i j hij hxi hxj
    have hx : x ∈ A i ∩ A j := ⟨hxi, hxj⟩
    rw [h.inter_eq i j hij] at hx
    exact hx
  -- locate the side of an edge
  have edge : ∀ {a b : V}, G.Adj a b → ∃ k, (H k).Adj a b ∧ a ∈ A k ∧ b ∈ A k := by
    intro a b hab
    rw [h.sup_eq, SimpleGraph.iSup_adj] at hab
    obtain ⟨k, hk⟩ := hab
    obtain ⟨ha, hb⟩ := h.support k hk
    exact ⟨k, hk, ha, hb⟩
  by_cases hsub : s.Subsingleton
  · rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · exact ⟨Classical.arbitrary ι, by simp, by simp⟩
    · have hxU : x ∈ ⋃ i, A i := by rw [h.union_eq]; trivial
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
      exact ⟨i, fun z hz => by rw [hsub hz hx]; exact hxi,
             SimpleGraph.IsClique.of_subsingleton hsub⟩
  · rw [Set.not_subsingleton_iff] at hsub
    obtain ⟨x, hx, y, hy, hxy⟩ := hsub
    obtain ⟨k, -, hxk, hyk⟩ := edge (hs hx hy hxy)
    -- at least one endpoint is not the cut vertex
    obtain ⟨p, hp, hpk, hpv⟩ : ∃ p, p ∈ s ∧ p ∈ A k ∧ p ≠ v := by
      by_cases hxv : x = v
      · exact ⟨y, hy, hyk, fun hyv => hxy (hxv.trans hyv.symm)⟩
      · exact ⟨x, hx, hxk, hxv⟩
    have hsub_k : s ⊆ A k := by
      intro z hz
      by_cases hzp : z = p
      · exact hzp ▸ hpk
      · obtain ⟨k', -, hzk', hpk'⟩ := edge (hs hz hp hzp)
        by_cases hkk : k' = k
        · exact hkk ▸ hzk'
        · exact absurd (cut hkk hpk' hpk) hpv
    refine ⟨k, hsub_k, ?_⟩
    intro z hz w hw hzw
    obtain ⟨k'', hk'', hzk'', hwk''⟩ := edge (hs hz hw hzw)
    by_cases hkk : k'' = k
    · exact hkk ▸ hk''
    · have hzv : z = v := cut hkk hzk'' (hsub_k hz)
      have hwv : w = v := cut hkk hwk'' (hsub_k hw)
      exact absurd (hzv.trans hwv.symm) hzw
