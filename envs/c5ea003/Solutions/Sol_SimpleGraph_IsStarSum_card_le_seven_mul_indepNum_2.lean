-- Prove2me | solution 2 for SimpleGraph.IsStarSum.card_le_seven_mul_indepNum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:07:46.853547+00:00
-- url     : https://prove2.me/submissions/cb449add-c0cf-4d36-ae6c-74ff2ea3eace

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily

open Finset SimpleGraph SimpleGraph.IsStarSum in
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [∀ i, DecidablePred (· ∈ A i)]
    {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
    (hdens : ∀ i, (Finset.univ.filter (· ∈ A i)).card ≤ 4 * (s i).card)
    (hside : ∀ i, 2 ≤ (Finset.univ.filter (· ∈ A i)).card)
    (hcover : Fintype.card V + (Fintype.card ι - 1)
      = ∑ i, (Finset.univ.filter (· ∈ A i)).card) :
    Fintype.card V ≤ 7 * G.indepNum := by
  classical
  -- two distinct sides meet only at the cut vertex
  have hmeet : ∀ (i j : ι), i ≠ j → ∀ x, x ∈ A i → x ∈ A j → x = v := by
    intro i j hij x hxi hxj
    have hx : x ∈ A i ∩ A j := ⟨hxi, hxj⟩
    rw [h.inter_eq i j hij] at hx
    exact hx
  -- every edge of `G` is an edge of some part
  have hadj : ∀ x y : V, G.Adj x y → ∃ i, (H i).Adj x y := by
    intro x y hxy
    rw [h.sup_eq] at hxy
    exact SimpleGraph.iSup_adj.1 hxy
  -- a family of independent sets avoiding the cut vertex unions to an independent set
  have hindep : ∀ u : ι → Finset V, (∀ i, ↑(u i) ⊆ A i) → (∀ i, (H i).IsIndepSet ↑(u i)) →
      (∀ i, v ∉ u i) → G.IsIndepSet ↑(Finset.univ.biUnion u) := by
    intro u hu hui huv x hx y hy hne hG
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hx hy
    obtain ⟨j, -, hxj⟩ := hx
    obtain ⟨k, -, hyk⟩ := hy
    obtain ⟨i, hHi⟩ := hadj x y hG
    have hxA : x ∈ A i := (h.support i hHi).1
    have hyA : y ∈ A i := (h.support i hHi).2
    have hxi : x ∈ u i := by
      by_cases hji : j = i
      · exact hji ▸ hxj
      · have hxv : x = v := hmeet j i hji x (hu j (Finset.mem_coe.2 hxj)) hxA
        rw [hxv] at hxj
        exact absurd hxj (huv j)
    have hyi : y ∈ u i := by
      by_cases hki : k = i
      · exact hki ▸ hyk
      · have hyv : y = v := hmeet k i hki y (hu k (Finset.mem_coe.2 hyk)) hyA
        rw [hyv] at hyk
        exact absurd hyk (huv k)
    exact (hui i) (Finset.mem_coe.2 hxi) (Finset.mem_coe.2 hyi) hne hHi
  -- the parts with the cut vertex removed
  have htsub : ∀ i, ↑((s i).erase v) ⊆ A i := by
    intro i x hx
    exact hs i (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hx)))
  have htindep : ∀ i, (H i).IsIndepSet ↑((s i).erase v) := by
    intro i
    refine Set.Pairwise.mono ?_ (hi i)
    intro x hx
    exact Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hx))
  have htv : ∀ i, v ∉ (s i).erase v := by
    intro i
    simp
  have hU : G.IsIndepSet ↑(Finset.univ.biUnion (fun i => (s i).erase v)) :=
    hindep _ htsub htindep htv
  have hdisj : (Finset.univ.biUnion (fun i => (s i).erase v)).card
      = ∑ i, ((s i).erase v).card := by
    refine Finset.card_biUnion ?_
    intro i _ j _ hij
    refine Finset.disjoint_left.2 ?_
    intro x hxi hxj
    have hxv : x = v := hmeet i j hij x (htsub i (Finset.mem_coe.2 hxi))
      (htsub j (Finset.mem_coe.2 hxj))
    rw [hxv] at hxi
    exact htv i hxi
  have hIU : ∑ i, ((s i).erase v).card ≤ G.indepNum := by
    rw [← hdisj]
    exact hU.card_le_indepNum
  -- a transversal of the sides is independent, so there are at most `indepNum` sides
  have hn_le : Fintype.card ι ≤ G.indepNum := by
    have hex : ∀ i : ι, ∃ x, x ∈ (Finset.univ.filter (· ∈ A i)).erase v := by
      intro i
      have hv : v ∈ Finset.univ.filter (· ∈ A i) := by
        simp [h.cut_mem i]
      have hc := Finset.card_erase_of_mem hv
      have h2 := hside i
      refine Finset.card_pos.1 ?_
      omega
    choose x hx using hex
    have hxA : ∀ i, x i ∈ A i := by
      intro i
      have := Finset.mem_of_mem_erase (hx i)
      simpa using this
    have hxv : ∀ i, x i ≠ v := fun i => Finset.ne_of_mem_erase (hx i)
    have hxinj : Function.Injective x := by
      intro i j hij
      by_contra hne
      have := hmeet i j hne (x i) (hxA i) (by rw [hij]; exact hxA j)
      exact hxv i this
    have hXcard : (Finset.univ.image x).card = Fintype.card ι := by
      rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ]
    have hXindep : G.IsIndepSet ↑(Finset.univ.image x) := by
      intro a ha b hb hne hG
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      obtain ⟨k, hHk⟩ := hadj _ _ hG
      have hak : x i ∈ A k := (h.support k hHk).1
      have hbk : x j ∈ A k := (h.support k hHk).2
      have hik : i = k := by
        by_contra hik
        exact hxv i (hmeet i k hik (x i) (hxA i) hak)
      have hjk : j = k := by
        by_contra hjk
        exact hxv j (hmeet j k hjk (x j) (hxA j) hbk)
      exact hne (by rw [hik, hjk])
    have := hXindep.card_le_indepNum
    omega
  -- `∑ |s i| + 1 ≤ indepNum + card ι`, using the cut vertex when every part contains it
  have hkey : ∑ i, (s i).card + 1 ≤ G.indepNum + Fintype.card ι := by
    by_cases hall : ∀ i, v ∈ s i
    · -- the cut vertex can be added to the union
      have hvnot : v ∉ Finset.univ.biUnion (fun i => (s i).erase v) := by
        simp
      have hins : G.IsIndepSet ↑(insert v (Finset.univ.biUnion (fun i => (s i).erase v))) := by
        intro a ha b hb hne hG
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
          Finset.mem_biUnion, Finset.mem_univ, true_and] at ha hb
        obtain ⟨i, hHi⟩ := hadj a b hG
        have haA : a ∈ A i := (h.support i hHi).1
        have hbA : b ∈ A i := (h.support i hHi).2
        have hmem : ∀ c : V, (c = v ∨ ∃ j, c ∈ (s j).erase v) → c ∈ A i → c ∈ s i := by
          intro c hc hcA
          rcases hc with rfl | ⟨j, hj⟩
          · exact hall i
          · by_cases hji : j = i
            · exact Finset.mem_of_mem_erase (hji ▸ hj)
            · have hcv : c = v := hmeet j i hji c (htsub j (Finset.mem_coe.2 hj)) hcA
              rw [hcv] at hj
              exact absurd hj (htv j)
        exact (hi i) (Finset.mem_coe.2 (hmem a ha haA)) (Finset.mem_coe.2 (hmem b hb hbA)) hne hHi
      have hcardins : (insert v (Finset.univ.biUnion (fun i => (s i).erase v))).card
          = ∑ i, ((s i).erase v).card + 1 := by
        rw [Finset.card_insert_of_notMem hvnot, hdisj]
      have hle := hins.card_le_indepNum
      rw [hcardins] at hle
      have hstep : ∀ i : ι, (s i).card = ((s i).erase v).card + 1 := by
        intro i
        rw [Finset.card_erase_of_mem (hall i)]
        have := Finset.card_pos.2 ⟨v, hall i⟩
        omega
      have hsum : ∑ i, (s i).card = ∑ i, ((s i).erase v).card + Fintype.card ι := by
        rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, smul_eq_mul, mul_one]
      omega
    · -- some part misses the cut vertex, so at most `card ι - 1` cards drop by one
      obtain ⟨i₀, hi₀⟩ : ∃ i, v ∉ s i := by
        by_contra hcon
        exact hall (fun i => not_not.1 (not_exists.1 hcon i))
      have hsplitS : (s i₀).card + ∑ i ∈ Finset.univ.erase i₀, (s i).card = ∑ i, (s i).card :=
        Finset.add_sum_erase Finset.univ (fun i => (s i).card) (Finset.mem_univ i₀)
      have hsplitT : ((s i₀).erase v).card
          + ∑ i ∈ Finset.univ.erase i₀, ((s i).erase v).card
          = ∑ i, ((s i).erase v).card :=
        Finset.add_sum_erase Finset.univ (fun i => ((s i).erase v).card) (Finset.mem_univ i₀)
      have hi₀eq : (s i₀).card = ((s i₀).erase v).card := by
        rw [Finset.erase_eq_of_notMem hi₀]
      have hrest : ∑ i ∈ Finset.univ.erase i₀, (s i).card
          ≤ ∑ i ∈ Finset.univ.erase i₀, (((s i).erase v).card + 1) := by
        refine Finset.sum_le_sum ?_
        intro i _
        have := Finset.pred_card_le_card_erase (s := s i) (a := v)
        omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ] at hrest
      have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
      omega
  -- put the counting together
  have hdenssum : ∑ i, (Finset.univ.filter (· ∈ A i)).card ≤ 4 * ∑ i, (s i).card := by
    calc ∑ i, (Finset.univ.filter (· ∈ A i)).card ≤ ∑ i, 4 * (s i).card :=
          Finset.sum_le_sum (fun i _ => hdens i)
      _ = 4 * ∑ i, (s i).card := by rw [Finset.mul_sum]
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  omega
