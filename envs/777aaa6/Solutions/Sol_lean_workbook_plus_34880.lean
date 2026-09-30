-- Prove2me | solution 1 for lean_workbook_plus_34880
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:47:09.435886+00:00
-- url     : https://prove2.me/submissions/031780ff-066b-4a54-aa18-16a0a7ecf823

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

namespace DenseProgression

open Finset

theorem midpoint_bound (N : ℕ) (S E : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hE : E ⊆ S) (hne : E.Nonempty)
    (hpar : ∀ x ∈ E, ∀ y ∈ E, x % 2 = y % 2)
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y = 2 * z → x = y) :
    S.card + 2 * E.card ≤ N + 3 := by
  let p := E.min' hne
  let q := E.max' hne
  have hp : p ∈ E := min'_mem E hne
  have hq : q ∈ E := max'_mem E hne
  have hmin : ∀ x ∈ E, p ≤ x := fun x hx => min'_le E x hx
  have hmax : ∀ x ∈ E, x ≤ q := fun x hx => le_max' E x hx
  have hmid : ∀ x ∈ E, ∀ y ∈ E, 2 * ((x + y) / 2) = x + y := by
    intro x hx y hy
    have := hpar x hx y hy
    omega
  let L := E.image fun x => (p + x) / 2
  let R := E.image fun x => (q + x) / 2
  have hL : L.card = E.card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    change (p + x) / 2 = (p + y) / 2 at hxy
    have hx' := hmid p hp x hx
    have hy' := hmid p hp y hy
    omega
  have hR : R.card = E.card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    change (q + x) / 2 = (q + y) / 2 at hxy
    have hx' := hmid q hq x hx
    have hy' := hmid q hq y hy
    omega
  have hinter : L ∩ R ⊆ {(p + q) / 2} := by
    intro z hz
    obtain ⟨hzL, hzR⟩ := mem_inter.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hzL
    obtain ⟨y, hy, hxy⟩ := mem_image.mp hzR
    have hx' := hmid p hp x hx
    have hy' := hmid q hq y hy
    have hpq := hmid p hp q hq
    have hxq := hmax x hx
    have hpy := hmin y hy
    simp only [mem_singleton]
    omega
  have hinter_card : (L ∩ R).card ≤ 1 := by
    simpa using card_le_card hinter
  have hmeet : S ∩ (L ∪ R) ⊆ {p, q} := by
    intro z hz
    obtain ⟨hzS, hzU⟩ := mem_inter.mp hz
    rcases mem_union.mp hzU with hzL | hzR
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hzL
      have hx' := hmid p hp x hx
      have hpx := hfree p (hE hp) x (hE hx) ((p + x) / 2) hzS (by omega)
      simp only [mem_insert, mem_singleton]
      left
      omega
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hzR
      have hx' := hmid q hq x hx
      have hqx := hfree q (hE hq) x (hE hx) ((q + x) / 2) hzS (by omega)
      simp only [mem_insert, mem_singleton]
      right
      omega
  have hmeet_card : (S ∩ (L ∪ R)).card ≤ 2 := by
    calc
      _ ≤ ({p, q} : Finset ℕ).card := card_le_card hmeet
      _ ≤ 2 := by simpa using card_insert_le p ({q} : Finset ℕ)
  have hrange : S ∪ (L ∪ R) ⊆ Icc 1 N := by
    intro z hz
    rcases mem_union.mp hz with hzS | hzU
    · exact hS hzS
    have hp' := mem_Icc.mp (hS (hE hp))
    have hq' := mem_Icc.mp (hS (hE hq))
    rcases mem_union.mp hzU with hzL | hzR
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hzL
      have hx' := mem_Icc.mp (hS (hE hx))
      have hm := hmid p hp x hx
      simp only [mem_Icc]
      omega
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hzR
      have hx' := mem_Icc.mp (hS (hE hx))
      have hm := hmid q hq x hx
      simp only [mem_Icc]
      omega
  have hrange_card : (S ∪ (L ∪ R)).card ≤ N := by
    simpa using card_le_card hrange
  have hLR := card_union_add_card_inter L R
  have hSU := card_union_add_card_inter S (L ∪ R)
  omega

theorem density_bound (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y = 2 * z → x = y) :
    2 * S.card ≤ N + 3 := by
  by_cases hzero : S.card = 0
  · omega
  let E := S.filter fun x => x % 2 = 0
  let O := S.filter fun x => ¬ x % 2 = 0
  have hEO : E.card + O.card = S.card := card_filter_add_card_filter_not _
  by_cases hlarge : O.card ≤ E.card
  · have hne : E.Nonempty := card_pos.mp (by omega)
    have hbound := midpoint_bound N S E hS (filter_subset _ _) hne
      (by intro x hx y hy; exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hfree
    omega
  · have hne : O.Nonempty := card_pos.mp (by omega)
    have hbound := midpoint_bound N S O hS (filter_subset _ _) hne
      (by
        intro x hx y hy
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        omega) hfree
    omega

theorem source (s : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 (4 * s))
    (hcard : S.card = 2 * s + 2) :
    ∃ x y z : ℕ, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x + y = 2 * z := by
  by_contra h
  have hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y = 2 * z → x = y := by
    intro x hx y hy z hz heq
    by_contra hxy
    exact h ⟨x, y, z, hx, hy, hz, hxy, by omega, by omega, heq⟩
  have hbound := density_bound (4 * s) S hS hfree
  omega

end DenseProgression

theorem solution (s : ℕ) (hs : s > 0) (A : Finset ℕ)
    (hA : A = Finset.Icc 1 (4 * s)) (hA' : A.card = 2 * s + 2) :
    ∃ x y z : ℕ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x + y = 2 * z := by
  exact DenseProgression.source s A (by rw [hA]) hA'
