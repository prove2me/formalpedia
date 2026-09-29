-- Prove2me | solution 1 for UnitalMagmaDefect.exists_comm_unital_magma_maximal_defect
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:01:38.640857+00:00
-- url     : https://prove2.me/submissions/0925c999-5708-4063-8503-309a10821b58

import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect

universe u

open Finset UnitalMagmaDefect in
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a) {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
    (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a)
    (m : ℕ) (hodd : Odd m) (hm : 3 ≤ m) :
    ∃ (M : Type) (_ : Mul M) (_ : One M) (_ : Fintype M) (_ : DecidableEq M),
      Fintype.card M = m + 1 ∧ (∀ a b : M, a * b = b * a) ∧ (∀ a : M, (1 : M) * a = a) ∧
        (∀ a : M, a * (1 : M) = a) ∧ defect M = m ^ 3 - m ^ 2 := by
  haveI : NeZero m := ⟨by omega⟩
  -- the witness: the negation magma on `ZMod m`
  let N := NegMagma (ZMod m)
  have hlN : ∀ y : N, (1 : N) * y = y := fun y => by rcases y with _ | b <;> rfl
  have hrN : ∀ y : N, y * (1 : N) = y := fun y => by rcases y with _ | b <;> rfl
  have hmul : ∀ a b : (ZMod m), (NegMagma.of a : N) * NegMagma.of b = NegMagma.of (-(a + b)) :=
    fun _ _ => rfl
  have hcase : ∀ x : N, x = 1 ∨ ∃ a, x = NegMagma.of a := fun x => by
    rcases x with _ | a
    · exact Or.inl rfl
    · exact Or.inr ⟨a, rfl⟩
  have hof_ne : ∀ a : (ZMod m), (NegMagma.of a : N) ≠ 1 := fun a h => by cases h
  have hof_inj : ∀ a b : (ZMod m), (NegMagma.of a : N) = NegMagma.of b ↔ a = b :=
    fun a b => ⟨fun h => Option.some.inj h, fun h => h ▸ rfl⟩
  -- `2` is invertible in `ZMod m` since `m` is odd
  obtain ⟨j, hj⟩ := hodd
  have h2 : ((j + 1 : ℕ) : (ZMod m)) * 2 = 1 := by
    have e : 2 * (j + 1) = m + 1 := by omega
    have h' : ((2 * (j + 1) : ℕ) : (ZMod m)) = 1 := by
      rw [e, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [← h']
    push_cast
    ring
  have hkey : ∀ a b c : (ZMod m), (-(-(a + b) + c) = -(a + -(b + c))) ↔ a = c := by
    intro a b c
    constructor
    · intro h
      have h' : 2 * (a - c) = 0 := by linear_combination h
      have : a - c = 0 := by
        calc a - c = ((j + 1 : ℕ) : (ZMod m)) * 2 * (a - c) := by rw [h2, one_mul]
          _ = ((j + 1 : ℕ) : (ZMod m)) * (2 * (a - c)) := by ring
          _ = 0 := by rw [h', mul_zero]
      exact sub_eq_zero.1 this
    · rintro rfl; ring
  -- the defect set is the image of the triples with `a ≠ c`
  let e : (ZMod m) × (ZMod m) × (ZMod m) ↪ N × N × N :=
    ⟨fun t => (NegMagma.of t.1, NegMagma.of t.2.1, NegMagma.of t.2.2), by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      simp only [Prod.mk.injEq, hof_inj] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl⟩
  have hset : defectSet N = (univ.filter fun t : (ZMod m) × (ZMod m) × (ZMod m) => t.1 ≠ t.2.2).map e := by
    ext ⟨x, y, z⟩
    simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      rcases hcase x with rfl | ⟨a, rfl⟩
      · exact (h (by simp only [hlN])).elim
      rcases hcase y with rfl | ⟨b, rfl⟩
      · exact (h (by simp only [hlN, hrN])).elim
      rcases hcase z with rfl | ⟨c, rfl⟩
      · exact (h (by simp only [hrN])).elim
      simp only [hmul, ne_eq, hof_inj, hkey] at h
      exact ⟨(a, b, c), h, rfl⟩
    · rintro ⟨⟨a, b, c⟩, hac, he⟩
      have hac' : a ≠ c := hac
      have hx : NegMagma.of a = x := congrArg Prod.fst he
      have hy : NegMagma.of b = y := congrArg (fun t => t.2.1) he
      have hz : NegMagma.of c = z := congrArg (fun t => t.2.2) he
      subst hx hy hz
      simp only [hmul, ne_eq, hof_inj, hkey]
      exact hac'
  have hcard : (univ.filter fun t : (ZMod m) × (ZMod m) × (ZMod m) => t.1 ≠ t.2.2).card = m ^ 3 - m ^ 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have hin : ∀ a : (ZMod m), (∑ c : (ZMod m), if a ≠ c then 1 else 0) = m - 1 := by
      intro a
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_ne, Finset.card_erase_of_mem
        (Finset.mem_univ a), Finset.card_univ, ZMod.card]
    simp only [hin, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    have h1 : 1 ≤ m := by omega
    have h3 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    zify [h1, h3]
    ring
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, hlN, hrN, ?_⟩
  · show Fintype.card (Option (ZMod m)) = m + 1
    rw [Fintype.card_option, ZMod.card]
  · intro x y
    rcases hcase x with rfl | ⟨a, rfl⟩ <;> rcases hcase y with rfl | ⟨b, rfl⟩
    · rfl
    · rw [hlN, hrN]
    · rw [hlN, hrN]
    · rw [hmul, hmul, add_comm]
  · rw [defect, hset, Finset.card_map, hcard]
