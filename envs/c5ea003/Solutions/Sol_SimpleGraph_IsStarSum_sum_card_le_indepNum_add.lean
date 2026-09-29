-- Prove2me | solution 1 for SimpleGraph.IsStarSum.sum_card_le_indepNum_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:51:38.960031+00:00
-- url     : https://prove2.me/submissions/6ae12117-9f35-4443-a779-a08216fc33f0

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

open SimpleGraph Finset

open SimpleGraph Finset in
/-- **Independent sets in the parts of a star sum** give an independent set of `G`, losing
at most one vertex per extra part. -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i)) :
    ∑ i, (s i).card ≤ G.indepNum + (Fintype.card ι - 1) := by
  classical
  have hinter : ∀ x i k, x ∈ A i → x ∈ A k → i ≠ k → x = v := by
    intro x i k hxi hxk hik
    have hm : x ∈ A i ∩ A k := ⟨hxi, hxk⟩
    rw [h.inter_eq i k hik] at hm
    exact hm
  have hadj : ∀ x y, G.Adj x y → ∃ k, (H k).Adj x y := by
    intro x y hxy
    rw [h.sup_eq, SimpleGraph.iSup_adj] at hxy
    exact hxy
  have hinU : ∀ x ∈ Finset.univ.biUnion (fun i => (s i).erase v), ∀ k, x ∈ A k → x ∈ s k := by
    intro x hx k hxk
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, -, hxi⟩ := hx
    rw [Finset.mem_erase] at hxi
    by_cases hik : i = k
    · exact hik ▸ hxi.2
    · exact absurd (hinter x i k (hs i hxi.2) hxk hik) hxi.1
  have indep : ∀ T : Finset V, (∀ x ∈ T, ∀ k, x ∈ A k → x ∈ s k) → G.IsIndepSet ↑T := by
    intro T hT x hx y hy hxy hG
    obtain ⟨k, hk⟩ := hadj x y hG
    exact hi k (hT x hx k (h.support k hk).1) (hT y hy k (h.support k hk).2) hxy hk
  have hdisj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (s i).erase v) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_erase] at hxi hxj
    exact hxi.1 (hinter x i j (hs i hxi.2) (hs j hxj.2) hij)
  have hcardU : (Finset.univ.biUnion (fun i => (s i).erase v)).card
      = ∑ i, ((s i).erase v).card := Finset.card_biUnion hdisj
  have hsplit : ∀ i, (s i).card = ((s i).erase v).card + (if v ∈ s i then 1 else 0) := by
    intro i
    split_ifs with hv
    · exact (Finset.card_erase_add_one hv).symm
    · rw [Finset.erase_eq_of_notMem hv, add_zero]
  have hsum : ∑ i, (s i).card
      = ∑ i, ((s i).erase v).card + ∑ i, (if v ∈ s i then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hsplit i)
  have hιpos : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hall : ∀ i, v ∈ s i
  · have hvU : v ∉ Finset.univ.biUnion (fun i => (s i).erase v) := by
      rw [Finset.mem_biUnion]
      rintro ⟨i, -, hvi⟩
      exact (Finset.mem_erase.mp hvi).1 rfl
    have hW : G.IsIndepSet ↑(insert v (Finset.univ.biUnion (fun i => (s i).erase v))) := by
      apply indep
      intro x hx k hxk
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hall k
      · exact hinU x hx k hxk
    have hle := hW.card_le_indepNum
    rw [Finset.card_insert_of_notMem hvU, hcardU] at hle
    have hind : ∑ i, (if v ∈ s i then 1 else 0) = Fintype.card ι := by
      simp [hall]
    rw [hsum, hind]
    omega
  · push_neg at hall
    obtain ⟨i0, hi0⟩ := hall
    have hle := (indep _ hinU).card_le_indepNum
    rw [hcardU] at hle
    have hind : ∑ i, (if v ∈ s i then 1 else 0) ≤ Fintype.card ι - 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0), if_neg hi0, add_zero]
      calc ∑ i ∈ Finset.univ.erase i0, (if v ∈ s i then 1 else 0)
          ≤ ∑ i ∈ Finset.univ.erase i0, 1 :=
            Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
        _ = Fintype.card ι - 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one,
              Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [hsum]
    omega
