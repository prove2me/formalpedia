-- Prove2me | solution 1 for SmoothSelfHint.asym_sym_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:08:40.850382+00:00
-- url     : https://prove2.me/submissions/fb5d99a7-10d0-47d0-bc50-e67e448a4116

import Mathlib
import Definitions.Def_Tropical_SmoothSelfHintDichotomyCore

open SmoothSelfHint Finset in
theorem solution (l : ℕ) [Fact (Nat.Prime l)] (hl : 2 < l) :
    (∀ n m : (ZMod l)ˣ, asymCondProb l n = asymCondProb l m) ∧
      (∃ n m : (ZMod l)ˣ, symCondProb l n ≠ symCondProb l m) := by
  -- the one-sided fibre over `n` is just `{(1, n)}`
  have hasym : ∀ n : (ZMod l)ˣ, (asymFiber ({1} : Finset (ZMod l)ˣ) n).card = 1 := by
    intro n
    rw [card_eq_one]
    refine ⟨(1, n), ?_⟩
    ext ⟨a, b⟩
    simp only [asymFiber, mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hab, rfl⟩
      exact ⟨rfl, by simpa using hab⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨one_mul _, rfl⟩
  -- the two-sided fibre has one point over `1` and two over `n ≠ 1`
  have hsym1 : (symFiber ({1} : Finset (ZMod l)ˣ) 1).card = 1 := by
    rw [card_eq_one]
    refine ⟨(1, 1), ?_⟩
    ext ⟨a, b⟩
    simp only [symFiber, mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hab, rfl | rfl⟩
      · exact ⟨rfl, by simpa using hab⟩
      · exact ⟨by simpa using hab, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨one_mul _, Or.inl rfl⟩
  have hsymn : ∀ n : (ZMod l)ˣ, n ≠ 1 → (symFiber ({1} : Finset (ZMod l)ˣ) n).card = 2 := by
    intro n hn
    rw [card_eq_two]
    refine ⟨(1, n), (n, 1), fun h => hn (Prod.mk.inj h).1.symm, ?_⟩
    ext ⟨a, b⟩
    simp only [symFiber, mem_filter, mem_univ, true_and, mem_singleton, mem_insert,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hab, rfl | rfl⟩
      · left
        exact ⟨rfl, by simpa using hab⟩
      · right
        exact ⟨by simpa using hab, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨one_mul _, Or.inl rfl⟩
      · exact ⟨mul_one _, Or.inr rfl⟩
  refine ⟨fun n m => by simp only [asymCondProb, hasym], ?_⟩
  haveI : Fact (2 < l) := ⟨hl⟩
  have hne : (-1 : (ZMod l)ˣ) ≠ 1 := fun h =>
    ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)
  refine ⟨1, -1, ?_⟩
  simp only [symCondProb, hsym1, hsymn (-1) hne]
  have hc : (Fintype.card (ZMod l)ˣ : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  intro h
  rw [div_left_inj' hc] at h
  norm_num at h
