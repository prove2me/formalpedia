-- Prove2me | solution 1 for lean_workbook_plus_45624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:07:45.325504+00:00
-- url     : https://prove2.me/submissions/5d7d122a-e69f-4a59-ab5d-29152cc68cb7

import Mathlib

set_option linter.unusedVariables false

open Finset

namespace PrimeMinusOneProductPartition

theorem nonzero_residue_product (p : ℕ) [Fact p.Prime] :
    (univ.erase (0 : ZMod p)).prod id = -1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hprod : (∏ k ∈ Ico 1 p, (k : ZMod p)) =
      (univ.erase (0 : ZMod p)).prod id := by
    refine prod_bij (fun k _ => (k : ZMod p)) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := mem_Ico.mp hk
      simp only [mem_erase, mem_univ, and_true]
      intro h
      have := congrArg ZMod.val h
      simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hk'.2] at this
      omega
    · intro k hk l hl h
      have := congrArg ZMod.val h
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.mp hk).2,
        Nat.mod_eq_of_lt (mem_Ico.mp hl).2] using this
    · intro z hz
      have hz0 : z ≠ 0 := (mem_erase.mp hz).1
      refine ⟨z.val, mem_Ico.mpr ⟨?_, ZMod.val_lt z⟩, ?_⟩
      · have : z.val ≠ 0 := by
          intro h
          apply hz0
          apply ZMod.val_injective p
          simpa only [ZMod.val_zero] using h
        omega
      · exact ZMod.natCast_zmod_val z
    · intro k hk
      rfl
  rw [← hprod, ZMod.prod_Ico_one_prime]

theorem residue_injective_partition (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (A B C : Finset ℤ) (hcard : A.card = p - 1)
    (hinj : Set.InjOn (fun z : ℤ => (z : ZMod p)) A)
    (hdisjoint : Disjoint B C) (hunion : B ∪ C = A) :
    B.prod id ≠ C.prod id := by
  letI : Fact p.Prime := ⟨hp⟩
  intro heq
  have hB : B ⊆ A := by rw [← hunion]; exact subset_union_left
  have hC : C ⊆ A := by rw [← hunion]; exact subset_union_right
  have heqmod : (∏ z ∈ B, (z : ZMod p)) = ∏ z ∈ C, (z : ZMod p) := by
    simpa only [Int.cast_prod, id_eq] using
      congrArg (fun z : ℤ => (z : ZMod p)) heq
  have hnonzero : ∀ z ∈ A, (z : ZMod p) ≠ 0 := by
    intro z hz hz0
    have hzBC : z ∈ B ∪ C := hunion.symm ▸ hz
    have hboth : (∏ x ∈ B, (x : ZMod p)) = 0 ∧
        (∏ x ∈ C, (x : ZMod p)) = 0 := by
      rcases mem_union.mp hzBC with hzB | hzC
      · have h := prod_eq_zero hzB hz0
        exact ⟨h, heqmod ▸ h⟩
      · have h := prod_eq_zero hzC hz0
        exact ⟨heqmod.symm ▸ h, h⟩
    obtain ⟨x, hx, hx0⟩ := prod_eq_zero_iff.mp hboth.1
    obtain ⟨y, hy, hy0⟩ := prod_eq_zero_iff.mp hboth.2
    have hxy : x = y := hinj (hB hx) (hC hy) (hx0.trans hy0.symm)
    exact disjoint_left.mp hdisjoint hx (hxy.symm ▸ hy)
  have himage : A.image (fun z : ℤ => (z : ZMod p)) = univ.erase 0 := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      simp only [mem_erase, mem_univ, and_true]
      exact hnonzero x hx
    · rw [card_image_iff.mpr hinj, hcard]
      simp only [card_erase_of_mem (mem_univ (0 : ZMod p)), card_univ, ZMod.card]
      exact le_rfl
  have htotal : (∏ z ∈ A, (z : ZMod p)) = -1 := by
    calc
      _ = (A.image (fun z : ℤ => (z : ZMod p))).prod id := by
        rw [prod_image hinj]
        rfl
      _ = -1 := by rw [himage]; exact nonzero_residue_product p
  have hsq : (∏ z ∈ B, (z : ZMod p)) ^ 2 = -1 := by
    rw [← htotal, ← hunion, prod_union hdisjoint, ← heqmod, pow_two]
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq hp4

theorem interval_cast_injective (p : ℕ) (hp : 0 < p) (a : ℤ) :
    Set.InjOn (fun z : ℤ => (z : ZMod p))
      (Ico a (a + ((p - 1 : ℕ) : ℤ)) : Finset ℤ) := by
  intro x hx y hy hxy
  have hx' := mem_Ico.mp hx
  have hy' := mem_Ico.mp hy
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp
  have hlen : ((p - 1 : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast Nat.sub_lt hp (by decide : 0 < 1)
  have hlow : -(p : ℤ) < y - x := by omega
  have hhigh : y - x < (p : ℤ) := by omega
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp hxy
  have hk0 : k = 0 := by
    by_contra h
    have : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases this with h | h <;> nlinarith
  rw [hk0, mul_zero] at hk
  omega

theorem source_partition (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (a : ℤ) (B C : Finset ℤ) (hdisjoint : Disjoint B C)
    (hunion : B ∪ C = Ico a (a + ((p - 1 : ℕ) : ℤ))) :
    B.prod id ≠ C.prod id := by
  apply residue_injective_partition p hp hp4 _ B C _
    (interval_cast_injective p hp.pos a) hdisjoint hunion
  simp only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]

theorem source_no_partition (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (a : ℤ) :
    ¬ ∃ B C : Finset ℤ, Disjoint B C ∧
      B ∪ C = Ico a (a + ((p - 1 : ℕ) : ℤ)) ∧ B.prod id = C.prod id := by
  rintro ⟨B, C, hd, hu, he⟩
  exact source_partition p hp hp4 a B C hd hu he

end PrimeMinusOneProductPartition

theorem solution (p : ℕ) (hp : p.Prime) (hp_mod_4_eq_3 : p ≡ 3 [ZMOD 4])
    (A : Finset ℤ) (hA : A.card = p - 1)
    (hA_consecutive : ∀ a : ℤ, a ∈ A ∧ a + 1 ∈ A) :
    ¬ (∃ B C : Finset ℤ, B ∪ C = A ∧ B.prod id = C.prod id) := by
  have hne : A.Nonempty := ⟨0, (hA_consecutive 0).1⟩
  have hm : A.max' hne + 1 ∈ A := (hA_consecutive (A.max' hne)).2
  have hle := le_max' A _ hm
  omega

#print axioms PrimeMinusOneProductPartition.nonzero_residue_product
#print axioms PrimeMinusOneProductPartition.residue_injective_partition
#print axioms PrimeMinusOneProductPartition.interval_cast_injective
#print axioms PrimeMinusOneProductPartition.source_partition
#print axioms PrimeMinusOneProductPartition.source_no_partition
#print axioms solution
