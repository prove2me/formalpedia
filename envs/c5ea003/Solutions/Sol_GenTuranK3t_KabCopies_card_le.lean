-- Prove2me | solution 1 for GenTuranK3t.KabCopies_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:48:47.961982+00:00
-- url     : https://prove2.me/submissions/35833cfd-cfce-476b-bc67-9992640ea8f0

import Mathlib
import Definitions.Def_Bridges_GenTuranAsymptoticBridge

open GenTuranK3t Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b t : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hcn : CNbound G t) :
    (KabCopies G a b).card
      ≤ (Fintype.card V).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by
  -- a chosen 3-subset of every set with at least three elements
  have hsel : ∀ S : Finset V, ∃ T ⊆ S, 3 ≤ S.card → T.card = 3 := by
    intro S
    by_cases h : 3 ≤ S.card
    · obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq h
      exact ⟨T, hT, fun _ => hTc⟩
    · exact ⟨∅, empty_subset _, fun h' => absurd h' h⟩
  choose sel hselS hselc using hsel
  -- encode a copy `(A, B)` as `(sel A, B, A \ sel A)`
  set X := (univ.powersetCard 3).biUnion (fun T => (powersetCard b (cnbhd G T)).biUnion
      (fun B => (powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R)))) with hX
  have hmaps : ∀ p ∈ KabCopies G a b, (sel p.1, p.2, p.1 \ sel p.1) ∈ X := by
    intro p hp
    simp only [KabCopies, mem_filter, mem_product, mem_powersetCard] at hp
    obtain ⟨⟨⟨-, hAc⟩, ⟨-, hBc⟩⟩, hdisj, hadj⟩ := hp
    have hT3 : (sel p.1).card = 3 := hselc p.1 (by omega)
    have hB3 : (sel p.2).card = 3 := hselc p.2 (by omega)
    rw [hX, mem_biUnion]
    refine ⟨sel p.1, mem_powersetCard.2 ⟨subset_univ _, hT3⟩, ?_⟩
    rw [mem_biUnion]
    refine ⟨p.2, mem_powersetCard.2 ⟨?_, hBc⟩, ?_⟩
    · intro v hv
      simp only [cnbhd, mem_filter, mem_univ, true_and]
      exact fun u hu => hadj u (hselS p.1 hu) v hv
    · rw [mem_image]
      refine ⟨p.1 \ sel p.1, mem_powersetCard.2 ⟨?_, ?_⟩, rfl⟩
      · intro w hw
        simp only [cnbhd, mem_filter, mem_univ, true_and]
        exact fun u hu => (hadj w (mem_sdiff.1 hw).1 u (hselS p.2 hu)).symm
      · rw [card_sdiff_of_subset (hselS p.1), hAc, hT3]
  have hinj : Set.InjOn (fun p : Finset V × Finset V => (sel p.1, p.2, p.1 \ sel p.1))
      (KabCopies G a b : Set (Finset V × Finset V)) := by
    intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Prod.ext
    · rw [← union_sdiff_of_subset (hselS p.1), ← union_sdiff_of_subset (hselS p'.1), h3, h1]
    · exact h2
  calc (KabCopies G a b).card ≤ X.card :=
        card_le_card_of_injOn _ (by intro p hp; exact mem_coe.2 (hmaps p (mem_coe.1 hp))) hinj
    _ ≤ ∑ T ∈ univ.powersetCard 3, ((powersetCard b (cnbhd G T)).biUnion
          (fun B => (powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R)))).card :=
        card_biUnion_le
    _ ≤ ∑ T ∈ univ.powersetCard 3, ((t - 1).choose b * (t - 1).choose (a - 3)) := by
        refine sum_le_sum fun T hT => ?_
        have hT3 : T.card = 3 := (mem_powersetCard.1 hT).2
        calc _ ≤ ∑ B ∈ powersetCard b (cnbhd G T),
              ((powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R))).card :=
              card_biUnion_le
          _ ≤ ∑ B ∈ powersetCard b (cnbhd G T), (t - 1).choose (a - 3) := by
              refine sum_le_sum fun B hB => ?_
              have hBc : B.card = b := (mem_powersetCard.1 hB).2
              refine card_image_le.trans ?_
              rw [card_powersetCard]
              exact Nat.choose_le_choose _ (hcn _ (hselc B (by omega)))
          _ = (powersetCard b (cnbhd G T)).card * (t - 1).choose (a - 3) := by
              rw [sum_const, smul_eq_mul]
          _ ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by
              rw [card_powersetCard]
              exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (hcn T hT3))
    _ = (Fintype.card V).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by
        rw [sum_const, smul_eq_mul, card_powersetCard, card_univ]
