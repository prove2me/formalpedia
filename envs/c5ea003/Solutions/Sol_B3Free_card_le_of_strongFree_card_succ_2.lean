-- Prove2me | solution 2 for B3Free.card_le_of_strongFree_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:09:41.207269+00:00
-- url     : https://prove2.me/submissions/e7902e98-be5f-46f3-b6a1-cbe3a41ce907

import Mathlib
import Definitions.Def_Bridges_B3FreeFamiliesBounds
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {d : ℕ}
    (hcard : Fintype.card α = d + 1) {F : Finset (Finset α)}
    (hF : StrongFree F (BoolLat d)) : F.card ≤ 2 ^ (d + 1) - 2 := by
  classical
  -- a distinguished point `a`, and `Fin d` embedded into the rest of `α`
  have hpos : 0 < Fintype.card α := by omega
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp hpos
  have hT : (Finset.univ.erase a).card = d := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard]
    rfl
  let e : Fin d ≃ (Finset.univ.erase a : Finset α) := (Finset.equivFinOfCardEq hT).symm
  let emb : Fin d ↪ α := ⟨fun i => (e i : α), fun i j h => e.injective (Subtype.ext h)⟩
  have hnot : ∀ S : BoolLat d, a ∉ S.map emb := by
    intro S hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hmem
    exact (Finset.mem_erase.mp (e i).2).1 hi
  -- the family avoiding `a` is a strong copy of `BoolLat d`
  have hι : IsStrongCopy (fun S : BoolLat d => S.map emb) := by
    refine ⟨fun S T h => Finset.map_injective emb h, fun p q => ?_⟩
    rw [Finset.map_ssubset_map]
    rfl
  -- ... and so is the family containing `a`
  have hι' : IsStrongCopy (fun S : BoolLat d => insert a (S.map emb)) := by
    refine ⟨fun S T h => ?_, fun p q => ?_⟩
    · have h' : S.map emb = T.map emb := by
        have := congrArg (fun X => X.erase a) h
        simpa [Finset.erase_insert (hnot S), Finset.erase_insert (hnot T)] using this
      exact Finset.map_injective emb h'
    · show insert a (p.map emb) ⊂ insert a (q.map emb) ↔ p ⊂ q
      rw [← Finset.map_ssubset_map (f := emb)]
      constructor
      · intro h
        rw [Finset.ssubset_iff_subset_ne] at h ⊢
        refine ⟨?_, fun heq => h.2 (by rw [heq])⟩
        intro x hx
        have hx' : x ∈ insert a (q.map emb) := h.1 (Finset.mem_insert_of_mem hx)
        rcases Finset.mem_insert.mp hx' with rfl | hq
        · exact absurd hx (hnot p)
        · exact hq
      · intro h
        rw [Finset.ssubset_iff_subset_ne] at h ⊢
        refine ⟨Finset.insert_subset_insert a h.1, fun heq => h.2 ?_⟩
        have := congrArg (fun X => X.erase a) heq
        simpa [Finset.erase_insert (hnot p), Finset.erase_insert (hnot q)] using this
  -- neither family fits inside `F`
  obtain ⟨S, hS⟩ : ∃ S : BoolLat d, S.map emb ∉ F := by
    by_contra h
    push_neg at h
    exact hF ⟨_, hι, h⟩
  obtain ⟨T, hT'⟩ : ∃ T : BoolLat d, insert a (T.map emb) ∉ F := by
    by_contra h
    push_neg at h
    exact hF ⟨_, hι', h⟩
  -- the two missing sets are distinct (only one contains `a`)
  have hne : S.map emb ≠ insert a (T.map emb) := by
    intro h
    exact hnot S (by rw [h]; exact Finset.mem_insert_self _ _)
  -- so `F` misses at least two of the `2^(d+1)` subsets
  have hsub : F ⊆ Finset.univ \ {S.map emb, insert a (T.map emb)} := by
    intro X hX
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨fun h => hS (h ▸ hX), fun h => hT' (h ▸ hX)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_finset, hcard,
    Finset.card_pair hne] at hle
  exact hle
