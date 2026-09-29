-- Prove2me | solution 2 for PosetFlow.chainAltSum_eq_neg_mu
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:51:43.214112+00:00
-- url     : https://prove2.me/submissions/80e0d5d1-aa88-44f9-a087-02ecc3475556

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    [LocallyFiniteOrder P] (x y : P) : chainAltSum x y = -mu ℤ x y := by
  classical
  have hmem : ∀ {a b : P} {C : Finset P}, C ∈ chainFinsets a b ↔
      a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, a ≤ c ∧ c ≤ b) ∧ (∀ c ∈ C, ∀ d ∈ C, c ≤ d ∨ d ≤ c) := by
    intro a b C
    simp only [chainFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
  -- the recursion: deleting the top element of a chain
  have hrec : ∀ {y : P}, x < y → chainAltSum x y = -∑ z ∈ Finset.Ico x y, chainAltSum x z := by
    intro y hxy
    -- chains `x ⋯ y` are chains `x ⋯ z` (`z < y` their second-largest element) with `y` added
    have key : ∑ p ∈ (Finset.Ico x y).sigma (fun z => chainFinsets x z), -((-1 : ℤ) ^ p.2.card)
        = ∑ C ∈ chainFinsets x y, (-1 : ℤ) ^ C.card := by
      refine Finset.sum_bij (fun p _ => insert y p.2) ?_ ?_ ?_ ?_
      · rintro ⟨z, D⟩ hp
        rw [Finset.mem_sigma, Finset.mem_Ico] at hp
        obtain ⟨⟨hxz, hzy⟩, hD⟩ := hp
        obtain ⟨hxD, hzD, hbd, hch⟩ := hmem.mp hD
        rw [hmem]
        refine ⟨Finset.mem_insert_of_mem hxD, Finset.mem_insert_self _ _, ?_, ?_⟩
        · intro c hc
          rcases Finset.mem_insert.mp hc with hcy | hc
          · rw [hcy]; exact ⟨hxy.le, le_rfl⟩
          · exact ⟨(hbd c hc).1, (hbd c hc).2.trans hzy.le⟩
        · intro c hc d hd
          rcases Finset.mem_insert.mp hc with hcy | hc <;>
            rcases Finset.mem_insert.mp hd with hdy | hd
          · rw [hcy, hdy]; exact Or.inl le_rfl
          · rw [hcy]; exact Or.inr ((hbd d hd).2.trans hzy.le)
          · rw [hdy]; exact Or.inl ((hbd c hc).2.trans hzy.le)
          · exact hch c hc d hd
      · rintro ⟨z, D⟩ hp ⟨z', D'⟩ hp' heq
        rw [Finset.mem_sigma, Finset.mem_Ico] at hp hp'
        obtain ⟨⟨_, hzy⟩, hD⟩ := hp
        obtain ⟨⟨_, hzy'⟩, hD'⟩ := hp'
        obtain ⟨_, hzD, hbd, _⟩ := hmem.mp hD
        obtain ⟨_, hzD', hbd', _⟩ := hmem.mp hD'
        have hyD : y ∉ D := fun h => absurd ((hbd y h).2) (not_le_of_gt hzy)
        have hyD' : y ∉ D' := fun h => absurd ((hbd' y h).2) (not_le_of_gt hzy')
        have hDD : D = D' := by
          have := congrArg (fun S => S.erase y) heq
          simpa [Finset.erase_insert hyD, Finset.erase_insert hyD'] using this
        subst hDD
        have hzz : z = z' := le_antisymm (hbd' z hzD).2 (hbd z' hzD').2
        subst hzz
        rfl
      · intro C hC
        obtain ⟨hxC, hyC, hbd, hch⟩ := hmem.mp hC
        have hxy' : x ≠ y := ne_of_lt hxy
        have hxD : x ∈ C.erase y := Finset.mem_erase.mpr ⟨hxy', hxC⟩
        obtain ⟨m, hm⟩ := Finset.exists_maximal ⟨x, hxD⟩
        have hmD : m ∈ C.erase y := hm.1
        obtain ⟨hmy, hmC⟩ := Finset.mem_erase.mp hmD
        have hle_m : ∀ c ∈ C.erase y, c ≤ m := by
          intro c hc
          rcases hch c (Finset.mem_erase.mp hc).2 m hmC with h | h
          · exact h
          · exact hm.2 hc h
        refine ⟨⟨m, C.erase y⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma, Finset.mem_Ico]
          refine ⟨⟨(hbd m hmC).1, lt_of_le_of_ne (hbd m hmC).2 hmy⟩, ?_⟩
          rw [hmem]
          refine ⟨hxD, hmD, fun c hc => ⟨(hbd c (Finset.mem_erase.mp hc).2).1, hle_m c hc⟩, ?_⟩
          intro c hc d hd
          exact hch c (Finset.mem_erase.mp hc).2 d (Finset.mem_erase.mp hd).2
        · exact Finset.insert_erase hyC
      · rintro ⟨z, D⟩ hp
        rw [Finset.mem_sigma, Finset.mem_Ico] at hp
        obtain ⟨⟨_, hzy⟩, hD⟩ := hp
        obtain ⟨_, _, hbd, _⟩ := hmem.mp hD
        have hyD : y ∉ D := fun h => absurd ((hbd y h).2) (not_le_of_gt hzy)
        show -((-1 : ℤ) ^ D.card) = (-1 : ℤ) ^ (insert y D).card
        rw [Finset.card_insert_of_notMem hyD, pow_succ]
        ring
    show ∑ C ∈ chainFinsets x y, (-1 : ℤ) ^ C.card = _
    rw [← key, Finset.sum_sigma]
    simp only [Finset.sum_neg_distrib, chainAltSum]

  -- strong induction on `y` (a finite poset is well founded)
  induction y using WellFoundedLT.induction with
  | _ y ih =>
    by_cases hxy : x ≤ y
    · rcases eq_or_lt_of_le hxy with rfl | hlt
      · -- the only chain from `x` to `x` is `{x}`
        have hC : chainFinsets x x = {{x}} := by
          ext C
          rw [hmem, Finset.mem_singleton]
          constructor
          · rintro ⟨hxC, -, hbd, -⟩
            ext a
            rw [Finset.mem_singleton]
            exact ⟨fun ha => le_antisymm (hbd a ha).2 (hbd a ha).1, fun ha => ha ▸ hxC⟩
          · rintro rfl
            refine ⟨Finset.mem_singleton_self x, Finset.mem_singleton_self x, ?_, ?_⟩
            · intro c hc
              rw [Finset.mem_singleton] at hc
              rw [hc]; exact ⟨le_rfl, le_rfl⟩
            · intro c hc d hd
              rw [Finset.mem_singleton] at hc hd
              rw [hc, hd]; exact Or.inl le_rfl
        rw [chainAltSum, hC, Finset.sum_singleton, Finset.card_singleton, mu_apply, if_pos rfl]
        norm_num
      · rw [hrec hlt, mu_apply, if_neg (ne_of_lt hlt), neg_neg,
          Finset.sum_congr rfl fun z hz => ih z (Finset.mem_Ico.mp hz).2,
          Finset.sum_neg_distrib, neg_neg]
    · -- no chains, and `μ` vanishes off the order
      have hC : chainFinsets x y = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro C hC
        obtain ⟨hxC, -, hbd, -⟩ := hmem.mp hC
        exact hxy (hbd x hxC).2
      have hne : x ≠ y := fun h => hxy (h ▸ le_rfl)
      have hIco : Finset.Ico x y = ∅ := Finset.Ico_eq_empty (fun h => hxy h.le)
      rw [chainAltSum, hC, Finset.sum_empty, mu_apply, if_neg hne, hIco, Finset.sum_empty]
      simp
