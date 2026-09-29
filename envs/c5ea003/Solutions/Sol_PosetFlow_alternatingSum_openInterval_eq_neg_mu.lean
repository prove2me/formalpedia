-- Prove2me | solution 1 for PosetFlow.alternatingSum_openInterval_eq_neg_mu
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:01:25.576293+00:00
-- url     : https://prove2.me/submissions/810bf53c-cc7f-4151-9ff3-5253738d7ecc

import Mathlib
import Definitions.Def_Algebra_PosetFlow_HallMobius
import Definitions.Def_Algebra_PosetFlow_IntervalEuler
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    [LocallyFiniteOrder P] {x y : P} (hxy : x < y) :
    ∑ F ∈ orderComplex (openInterval x y), (-1 : ℤ) ^ F.card = -mu ℤ x y := by
  -- Philip Hall's theorem: the alternating chain sum is `-μ`
  have hall : ∀ x y : P, chainAltSum x y = -mu ℤ x y := by
    intro x y
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

  classical
  rw [← hall x y]
  show _ = ∑ C ∈ chainFinsets x y, (-1 : ℤ) ^ C.card
  have hmemC : ∀ {C : Finset P}, C ∈ chainFinsets x y ↔
      x ∈ C ∧ y ∈ C ∧ (∀ c ∈ C, x ≤ c ∧ c ≤ y) ∧ (∀ c ∈ C, ∀ d ∈ C, c ≤ d ∨ d ≤ c) := by
    intro C
    simp only [chainFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemF : ∀ {F : Finset (openInterval x y)},
      F ∈ orderComplex (openInterval x y) ↔ IsOrderChain F := by
    intro F
    simp only [orderComplex, Finset.mem_filter, Finset.mem_univ, true_and]
  -- a face is recovered from the chain obtained by adjoining both endpoints
  have hkey : ∀ (F : Finset (openInterval x y)) (a : openInterval x y),
      a ∈ F ↔ a.val ∈ insert x (insert y (F.image Subtype.val)) := by
    intro F a
    have ha := Finset.mem_Ioo.mp a.2
    simp only [Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      exact Or.inr (Or.inr ⟨a, h, rfl⟩)
    · rintro (h | h | ⟨b, hb, hba⟩)
      · exact absurd h (ne_of_gt ha.1)
      · exact absurd h (ne_of_lt ha.2)
      · rwa [← Subtype.ext hba]
  refine Finset.sum_bij (fun F _ => insert x (insert y (F.image Subtype.val))) ?_ ?_ ?_ ?_
  · -- adjoining the endpoints gives a chain from `x` to `y`
    intro F hF
    have hch := hmemF.mp hF
    have hbd : ∀ e ∈ insert x (insert y (F.image Subtype.val)), x ≤ e ∧ e ≤ y := by
      intro e he
      rcases Finset.mem_insert.mp he with hex | he'
      · rw [hex]; exact ⟨le_rfl, hxy.le⟩
      rcases Finset.mem_insert.mp he' with hey | he''
      · rw [hey]; exact ⟨hxy.le, le_rfl⟩
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he''
      have := Finset.mem_Ioo.mp a.2
      exact ⟨this.1.le, this.2.le⟩
    rw [hmemC]
    refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      hbd, ?_⟩
    intro c hc d hd
    rcases Finset.mem_insert.mp hc with hcx | hc'
    · rw [hcx]; exact Or.inl (hbd d hd).1
    rcases Finset.mem_insert.mp hc' with hcy | hc''
    · rw [hcy]; exact Or.inr (hbd d hd).2
    rcases Finset.mem_insert.mp hd with hdx | hd'
    · rw [hdx]; exact Or.inr (hbd c hc).1
    rcases Finset.mem_insert.mp hd' with hdy | hd''
    · rw [hdy]; exact Or.inl (hbd c hc).2
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc''
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd''
    exact hch a ha b hb
  · -- injective
    intro F _ F' _ heq
    ext a
    rw [hkey F a, hkey F' a]
    exact Iff.of_eq (congrArg (a.val ∈ ·) heq)
  · -- surjective: keep the interior of a chain
    intro C hC
    obtain ⟨hxC, hyC, hbd, hch⟩ := hmemC.mp hC
    refine ⟨C.subtype (· ∈ Finset.Ioo x y), ?_, ?_⟩
    · rw [hmemF]
      intro a ha b hb
      rw [Finset.mem_subtype] at ha hb
      exact hch _ ha _ hb
    · ext c
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_subtype]
      constructor
      · rintro (h | h | ⟨a, ha, rfl⟩)
        · rw [h]; exact hxC
        · rw [h]; exact hyC
        · exact ha
      · intro hc
        by_cases hcx : c = x
        · exact Or.inl hcx
        by_cases hcy : c = y
        · exact Or.inr (Or.inl hcy)
        exact Or.inr (Or.inr ⟨⟨c, Finset.mem_Ioo.mpr ⟨lt_of_le_of_ne (hbd c hc).1 (Ne.symm hcx),
          lt_of_le_of_ne (hbd c hc).2 hcy⟩⟩, hc, rfl⟩)
  · -- two extra vertices do not change the sign
    intro F _
    have hx : x ∉ insert y (F.image Subtype.val) := by
      rw [Finset.mem_insert, Finset.mem_image]
      rintro (h | ⟨a, -, ha⟩)
      · exact ne_of_lt hxy h
      · exact ne_of_gt (Finset.mem_Ioo.mp a.2).1 ha
    have hy : y ∉ F.image Subtype.val := by
      rw [Finset.mem_image]
      rintro ⟨a, -, ha⟩
      exact ne_of_lt (Finset.mem_Ioo.mp a.2).2 ha
    show (-1 : ℤ) ^ F.card = (-1 : ℤ) ^ (insert x (insert y (F.image Subtype.val))).card
    rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy,
      Finset.card_image_of_injective _ Subtype.val_injective]
    ring
