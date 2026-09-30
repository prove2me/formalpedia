-- Prove2me | solution 1 for lean_workbook_plus_58008
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:24:19.888796+00:00
-- url     : https://prove2.me/submissions/94e087bd-46d0-4ee2-a41c-39a5279084e7

import Mathlib

set_option linter.unusedVariables false

open Finset

namespace FinitePrimeShiftAdmissibility

def Good (P : Finset ℕ) (H : Finset ℤ) (t : ℤ) : Prop :=
  ∀ p ∈ P, ∀ h ∈ H, ¬ (p : ℤ) ∣ t + h

def Admissible (P : Finset ℕ) (H : Finset ℤ) : Prop :=
  ∀ p ∈ P, ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

theorem good_iff_zmod (P : Finset ℕ) (H : Finset ℤ) (t : ℤ) :
    Good P H t ↔ ∀ p ∈ P, ∀ h ∈ H, (t : ZMod p) + (h : ZMod p) ≠ 0 := by
  simp only [Good, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add]

theorem admissible_of_good (P : Finset ℕ) (H : Finset ℤ) (t : ℤ)
    (ht : Good P H t) : Admissible P H := by
  intro p hp
  refine ⟨-(t : ZMod p), ?_⟩
  intro h hh he
  apply (good_iff_zmod P H t).mp ht p hp h hh
  rw [he, add_neg_cancel]

theorem good_add_multiple (P : Finset ℕ) (H : Finset ℤ) (t k : ℤ) :
    Good P H (t + (P.prod id : ℕ) * k) ↔ Good P H t := by
  rw [good_iff_zmod, good_iff_zmod]
  have hz : ∀ p ∈ P, ((P.prod id : ℕ) : ZMod p) = 0 := by
    intro p hp
    obtain ⟨k, hk⟩ := dvd_prod_of_mem id hp
    rw [hk, Nat.cast_mul, id_eq, ZMod.natCast_self, zero_mul]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  constructor <;> intro ht p hp h hh
  · simpa only [hz p hp, zero_mul, add_zero] using ht p hp h hh
  · simpa only [hz p hp, zero_mul, add_zero] using ht p hp h hh

theorem exists_good_nat (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hH : Admissible P H) :
    ∃ t : ℕ, Good P H t := by
  classical
  have hchoice : ∀ p : ℕ, ∃ r : ZMod p,
      p ∈ P → ∀ h ∈ H, (h : ZMod p) ≠ r := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨r, hr⟩ := hH p hp
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun hm => (hp hm).elim⟩
  choose r hr using hchoice
  have hn : ∀ p ∈ P, p ≠ 0 := fun p hp => (hP p hp).ne_zero
  have hc : Set.Pairwise (P : Set ℕ) (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (hP p hp).coprime_iff_not_dvd.mpr (by
      intro hd
      have he := (Nat.dvd_prime (hP q hq)).mp hd
      rcases he with he | he
      · exact (hP p hp).ne_one he
      · exact hpq he)
  let t := Nat.chineseRemainderOfFinset (fun p => (-r p).val) id P hn hc
  refine ⟨t.val, (good_iff_zmod P H t.val).mpr ?_⟩
  intro p hp h hh he
  letI : NeZero p := ⟨hn p hp⟩
  have ht : (t.val : ZMod p) = -r p := by
    have heq : (t.val : ZMod p) = ((-r p).val : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff t.val (-r p).val p).mpr (t.property p hp)
    exact heq.trans (ZMod.natCast_zmod_val (-r p))
  have he' : -(r p) + (h : ZMod p) = 0 := by simpa only [Int.cast_natCast, ht] using he
  exact hr p hp h hh (by linear_combination he')

theorem arbitrarily_large_good (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hH : Admissible P H) (N : ℕ) :
    ∃ t : ℕ, N < t ∧ Good P H t := by
  obtain ⟨t, ht⟩ := exists_good_nat P H hP hH
  have hM : 0 < P.prod id := prod_pos (fun p hp => (hP p hp).pos)
  refine ⟨t + P.prod id * (N + 1), ?_, ?_⟩
  · nlinarith
  · have := (good_add_multiple P H t (N + 1)).mpr ht
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using this

theorem exists_iff_admissible (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∃ t : ℤ, Good P H t) ↔ Admissible P H := by
  constructor
  · rintro ⟨t, ht⟩
    exact admissible_of_good P H t ht
  · intro h
    obtain ⟨t, ht⟩ := exists_good_nat P H hP h
    exact ⟨t, ht⟩

theorem infinite_positive_iff (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    {t : ℕ | 0 < t ∧ Good P H t}.Infinite ↔ Admissible P H := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.nonempty
    exact admissible_of_good P H t ht.2
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨t, hNt, ht⟩ := arbitrarily_large_good P H hP h N
    exact ⟨t, ⟨by omega, ht⟩, hNt⟩

theorem missing_residue_iff_card (p : ℕ) (hp : 0 < p) (H : Finset ℤ) :
    (∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ↔
      (H.image (fun h : ℤ => (h : ZMod p))).card < p := by
  classical
  letI : NeZero p := ⟨ne_of_gt hp⟩
  constructor
  · rintro ⟨r, hr⟩
    have hn : r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      rintro hm
      obtain ⟨h, hh, he⟩ := mem_image.mp hm
      exact hr h hh he
    have hs : H.image (fun h : ℤ => (h : ZMod p)) ⊂ univ := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨subset_univ _, ?_⟩
      intro he
      exact hn (he.symm ▸ mem_univ r)
    simpa only [card_univ, ZMod.card] using card_lt_card hs
  · intro hc
    have hn : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      by_contra h
      push_neg at h
      have he : H.image (fun h : ℤ => (h : ZMod p)) = univ := eq_univ_of_forall h
      rw [he, card_univ, ZMod.card] at hc
      omega
    obtain ⟨r, hr⟩ := hn
    refine ⟨r, ?_⟩
    intro h hh he
    exact hr (mem_image.mpr ⟨h, hh, he⟩)

theorem admissible_iff_card (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    Admissible P H ↔
      ∀ p ∈ P, (H.image (fun h : ℤ => (h : ZMod p))).card < p := by
  constructor <;> intro h p hp
  · exact (missing_residue_iff_card p (hP p hp).pos H).mp (h p hp)
  · exact (missing_residue_iff_card p (hP p hp).pos H).mpr (h p hp)

theorem small_offsets_suffice (P : Finset ℕ) (H : Finset ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hsmall : ∀ p ∈ P, H.card < p) :
    {t : ℕ | 0 < t ∧ Good P H t}.Infinite := by
  apply (infinite_positive_iff P H hP).mpr
  apply (admissible_iff_card P H hP).mpr
  intro p hp
  exact lt_of_le_of_lt card_image_le (hsmall p hp)

theorem source_obstruction : ¬ ∃ t : ℤ, Good {2} {0, 1} t := by
  rintro ⟨t, ht⟩
  have h0 := ht 2 (by simp) 0 (by simp)
  have h1 := ht 2 (by simp) 1 (by simp)
  simp only [add_zero, Int.dvd_iff_emod_eq_zero] at h0 h1
  omega

theorem source_false_despite_offsets :
    (∀ r : ℕ, ¬ (2 : ℕ) ∣ (fun _ : ℕ => 1) r) ∧
      ¬ ∃ t : ℕ, ¬ 2 ∣ t ∧ ∀ r : ℕ, ¬ 2 ∣ t + (fun _ : ℕ => 1) r := by
  constructor
  · intro r
    norm_num
  · rintro ⟨t, ht, hr⟩
    have h1 := hr 0
    simp only [Nat.dvd_iff_mod_eq_zero] at ht h1
    omega

end FinitePrimeShiftAdmissibility

theorem solution (P : Finset ℕ) (n : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hn : ∀ r, ¬ ∃ p ∈ P, p ∣ n r) :
    ∃ t, ∀ p ∈ P, ¬ p ∣ t + n 0 := by
  refine ⟨0, ?_⟩
  intro p hp hd
  exact hn 0 ⟨p, hp, by simpa only [zero_add] using hd⟩

#print axioms FinitePrimeShiftAdmissibility.Good
#print axioms FinitePrimeShiftAdmissibility.Admissible
#print axioms FinitePrimeShiftAdmissibility.good_iff_zmod
#print axioms FinitePrimeShiftAdmissibility.admissible_of_good
#print axioms FinitePrimeShiftAdmissibility.good_add_multiple
#print axioms FinitePrimeShiftAdmissibility.exists_good_nat
#print axioms FinitePrimeShiftAdmissibility.arbitrarily_large_good
#print axioms FinitePrimeShiftAdmissibility.exists_iff_admissible
#print axioms FinitePrimeShiftAdmissibility.infinite_positive_iff
#print axioms FinitePrimeShiftAdmissibility.missing_residue_iff_card
#print axioms FinitePrimeShiftAdmissibility.admissible_iff_card
#print axioms FinitePrimeShiftAdmissibility.small_offsets_suffice
#print axioms FinitePrimeShiftAdmissibility.source_obstruction
#print axioms FinitePrimeShiftAdmissibility.source_false_despite_offsets
#print axioms solution
