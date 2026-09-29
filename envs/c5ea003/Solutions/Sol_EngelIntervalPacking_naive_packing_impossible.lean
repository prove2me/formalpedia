-- Prove2me | solution 1 for EngelIntervalPacking.naive_packing_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:58:41.652352+00:00
-- url     : https://prove2.me/submissions/7198833f-0023-468c-8b83-4680189fa054

import Mathlib
import Definitions.Def_Applications_PosetTheory_EngelIntervalPacking

open Finset EngelIntervalPacking in
theorem solution (n l r : ℕ) (hl : 1 ≤ l) (hln : l ≤ n) (hr : 1 ≤ r) :
    ¬ ∃ f, IsNaivePacking n l r f := by
  rintro ⟨f, hvalid, hnaive⟩
  -- the bottom `T = {0, …, l-1}` and one element `c` of its `C`-set
  have hT : IsLSet n l (Finset.range l) := ⟨Finset.range_mono hln, Finset.card_range l⟩
  obtain ⟨hfsub, hfcard, hdisj⟩ := hvalid _ hT
  obtain ⟨c, hc⟩ : (f (Finset.range l)).Nonempty := Finset.card_pos.1 (by omega)
  have hcT : c ∉ Finset.range l := Finset.disjoint_right.1 hdisj hc
  have h0 : 0 ∈ Finset.range l := Finset.mem_range.2 (by omega)
  -- swapping `0` for `c` gives another `l`-set inside `T ∪ f T`
  have hT' : IsLSet n l (insert c ((Finset.range l).erase 0)) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hfsub hc
      · exact hT.1 (Finset.mem_of_mem_erase hx)
    · rw [Finset.card_insert_of_notMem (fun h => hcT (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem h0, Finset.card_range]
      omega
  have hne : insert c ((Finset.range l).erase 0) ≠ Finset.range l := by
    intro h
    apply hcT
    rw [← h]
    exact Finset.mem_insert_self c _
  have hsub : insert c ((Finset.range l).erase 0) ⊆ Finset.range l ∪ f (Finset.range l) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_union_right _ hc
    · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hx)
  exact (hnaive _ hT' _ hT hne).1 hsub
