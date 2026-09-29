-- Prove2me | solution 2 for PosetFlow.chainAltSum_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:39:59.827117+00:00
-- url     : https://prove2.me/submissions/b4c6e264-f958-4aa4-b509-e0395b73ec33

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    [LocallyFiniteOrder P] {x y : P} (hxy : x < y) :
    chainAltSum x y = -∑ z ∈ Finset.Ico x y, chainAltSum x z := by
  classical
  have hmem : ∀ {a b : P} {C : Finset P}, C ∈ chainFinsets a b ↔
      a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, a ≤ c ∧ c ≤ b) ∧ (∀ c ∈ C, ∀ d ∈ C, c ≤ d ∨ d ≤ c) := by
    intro a b C
    simp only [chainFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
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
