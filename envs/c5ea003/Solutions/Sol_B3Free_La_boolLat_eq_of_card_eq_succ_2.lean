-- Prove2me | solution 2 for B3Free.La_boolLat_eq_of_card_eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:05:33.107499+00:00
-- url     : https://prove2.me/submissions/de1dac2e-cf2f-4f70-8639-6b86131bb891

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {d : ℕ}
    (hcard : Fintype.card α = d + 1) : La α (BoolLat d) = 2 ^ (d + 1) - 2 := by
  classical
  -- ===== the strong-free counting bound (`card_le_of_strongFree_card_succ`) =====
  have hbound : ∀ F : Finset (Finset α), StrongFree F (BoolLat d) → F.card ≤ 2 ^ (d + 1) - 2 := by
    intro F hF
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
  -- a weak copy is in particular a strong copy's weakening, so weak-free ⇒ strong-free
  have hws : ∀ F : Finset (Finset α), WeakFree F (BoolLat d) → StrongFree F (BoolLat d) := by
    intro F hW ⟨ι, ⟨hinj, hiff⟩, hmem⟩
    exact hW ⟨ι, ⟨hinj, fun p q hpq => (hiff p q).mpr hpq⟩, hmem⟩
  -- ===== the extremal family: every nonempty proper subset =====
  set F₀ : Finset (Finset α) := Finset.univ.filter (fun X => X ≠ ∅ ∧ X ≠ Finset.univ) with hF₀
  have hpos : 0 < Fintype.card α := by omega
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp hpos
  have hne0 : (∅ : Finset α) ≠ Finset.univ := by
    intro h
    have : a ∈ (∅ : Finset α) := h ▸ Finset.mem_univ a
    simp at this
  have hF₀card : F₀.card = 2 ^ (d + 1) - 2 := by
    have hF₀eq : F₀ = Finset.univ \ {∅, Finset.univ} := by
      ext X
      simp [hF₀, not_or]
    rw [hF₀eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_finset, hcard,
      Finset.card_pair hne0]
  -- `F₀` is weak `BoolLat d`-free: a weak copy would contain a strict chain of `d+1` sets,
  -- needing `d+1` distinct sizes inside `{1, …, d}`
  have hF₀free : WeakFree F₀ (BoolLat d) := by
    rintro ⟨ι, ⟨hinj, hmono⟩, hmem⟩
    let C : ℕ → BoolLat d := fun k => Finset.univ.filter (fun i : Fin d => (i : ℕ) < k)
    have hstep : ∀ k, k < d → C k ⊂ C (k + 1) := by
      intro k hk
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨⟨k, hk⟩, ?_, ?_⟩
        · simp [C]
        · simp [C]
      · intro i hi
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        omega
    have hmemF : ∀ p : BoolLat d, ι p ≠ ∅ ∧ ι p ≠ Finset.univ := by
      intro p
      have := hmem p
      simp only [hF₀, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hgrow : ∀ k, k ≤ d → k + 1 ≤ (ι (C k)).card := by
      intro k
      induction k with
      | zero =>
        intro _
        exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (hmemF _).1)
      | succ j ih =>
        intro hj
        have hlt : ι (C j) ⊂ ι (C (j + 1)) := hmono _ _ (hstep j (by omega))
        have := Finset.card_lt_card hlt
        have := ih (by omega)
        omega
    have hfull : (ι (C d)).card = Fintype.card α := by
      have h1 := hgrow d le_rfl
      have h2 : (ι (C d)).card ≤ Fintype.card α := Finset.card_le_univ _
      omega
    exact (hmemF (C d)).2 (Finset.eq_univ_of_card _ hfull)
  -- ===== assemble: `La` is exactly this bound =====
  apply le_antisymm
  · refine Finset.sup_le fun F hF => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    exact hbound F (hws F hF)
  · rw [← hF₀card]
    exact Finset.le_sup (f := Finset.card) (by simp [hF₀free])
