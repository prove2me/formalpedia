-- Prove2me | solution 1 for mme_dwz_paired_product_type_card_and_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:21:13.722406+00:00
-- url     : https://prove2.me/submissions/c963f74f-831a-49f1-9d03-3c38375dc2d5

import Theorems.Thm_mme_prescribed_cell_histogram_card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

open BigOperators
open scoped Classical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZPairedTypical

open MME.RecursiveYZ

theorem product_counts_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (l : A → ℕ) (r : B → ℕ) (DL DR m : ℕ)
    (hl : ∑ a, l a = DL) (hr : ∑ b, r b = DR) :
    (∑ ab : A × B, m * l ab.1 * r ab.2) = m * DL * DR := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hr]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hl]

/-- Denominators are cleared explicitly: one ordered pair type has
`m * DL * DR` paired positions, and joint counts `m * l(a) * r(b)`.
The positions remain paired throughout this count. -/
theorem paired_product_profile_card
    {P S A B : Type*} [Fintype P] [Fintype S] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ)
    (DL DR m : S → ℕ)
    (hl : ∀ s, ∑ a, l s a = DL s) (hr : ∀ s, ∑ b, r s b = DR s)
    (hsize : ∀ s, Fintype.card {p : P // cell p = s} = m s * DL s * DR s) :
    Fintype.card {f : P → A × B //
      Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f} =
      ∏ s, Nat.multinomial Finset.univ (fun ab : A × B =>
        m s * l s ab.1 * r s ab.2) := by
  have hsum (s : S) :
      (∑ ab : A × B, m s * l s ab.1 * r s ab.2) =
        Fintype.card {p : P // cell p = s} :=
    (product_counts_sum (l s) (r s) (DL s) (DR s) (m s) (hl s) (hr s)).trans
      (hsize s).symm
  rw [mme_prescribed_cell_histogram_card cell _ hsum]
  apply Finset.prod_congr rfl
  intro s _
  rw [Nat.multinomial, hsum]

theorem paired_product_profile_nonempty
    {P S A B : Type*} [Fintype P] [Fintype S] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ)
    (DL DR m : S → ℕ)
    (hl : ∀ s, ∑ a, l s a = DL s) (hr : ∀ s, ∑ b, r s b = DR s)
    (hsize : ∀ s, Fintype.card {p : P // cell p = s} = m s * DL s * DR s) :
    ∃ f : P → A × B, Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f := by
  have hp : 0 < Fintype.card {f : P → A × B //
      Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f} := by
    rw [paired_product_profile_card cell l r DL DR m hl hr hsize]
    exact Finset.prod_pos (fun _ _ => Nat.multinomial_pos _ _)
  obtain ⟨f⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨f.1, f.2⟩

theorem count_fst
    {P S A B : Type*} [Fintype P] [Fintype B]
    (cell : P → S) (f : P → A × B) (s : S) (a : A) :
    count cell (fun p => (f p).1) s a = ∑ b, count cell f s (a, b) := by
  classical
  unfold count
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : P => cell p = s ∧ (f p).1 = a))
    (t := Finset.univ) (f := fun p => (f p).2)
    (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.filter_filter, Prod.ext_iff, and_assoc] using h

theorem count_snd
    {P S A B : Type*} [Fintype P] [Fintype A]
    (cell : P → S) (f : P → A × B) (s : S) (b : B) :
    count cell (fun p => (f p).2) s b = ∑ a, count cell f s (a, b) := by
  classical
  unfold count
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : P => cell p = s ∧ (f p).2 = b))
    (t := Finset.univ) (f := fun p => (f p).1)
    (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.filter_filter, Prod.ext_iff, and_assoc, and_left_comm,
    and_comm] using h

theorem paired_product_profile_marginals
    {P S A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ)
    (DL DR m : S → ℕ)
    (hl : ∀ s, ∑ a, l s a = DL s) (hr : ∀ s, ∑ b, r s b = DR s)
    (f : P → A × B)
    (hf : Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f) :
    (∀ s a, count cell (fun p => (f p).1) s a = m s * l s a * DR s) ∧
    (∀ s b, count cell (fun p => (f p).2) s b = m s * DL s * r s b) := by
  unfold Useful at hf
  constructor
  · intro s a
    rw [count_fst]
    simp_rw [hf]
    rw [← Finset.mul_sum, hr]
  · intro s b
    rw [count_snd]
    simp_rw [hf]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hl]

/-- Aggregate a prescribed cell profile through any cell-dependent tag.
This is the exact finite pushforward used for the four-quarter histogram. -/
theorem prescribed_profile_pushforward
    {P S A T : Type*} [Fintype P] [Fintype S] [Fintype A]
    (cell : P → S) (f : P → A) (mu : S → A → ℕ)
    (hf : Useful cell mu f) (tag : S → A → T) (t : T) :
    Fintype.card {p : P // tag (cell p) (f p) = t} =
      ∑ s, ∑ a, if tag s a = t then mu s a else 0 := by
  classical
  rw [Fintype.card_subtype,
    ← Fintype.sum_prod_type (fun sa : S × A =>
      if tag sa.1 sa.2 = t then mu sa.1 sa.2 else 0)]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : P => tag (cell p) (f p) = t))
    (t := Finset.univ) (f := fun p => (cell p, f p))
    (fun _ _ => Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro sa _
  by_cases ht : tag sa.1 sa.2 = t
  · rw [if_pos ht, ← hf sa.1 sa.2]
    unfold count
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    constructor
    · exact fun hp => hp.2
    · intro hp
      exact ⟨by simpa only [hp.1, hp.2] using ht, hp⟩
  · rw [if_neg ht]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff] at hp
    exact ht (by simpa only [hp.2.1, hp.2.2] using hp.1)

theorem paired_product_profile_pushforward
    {P S A B T : Type*} [Fintype P] [Fintype S] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ) (m : S → ℕ)
    (f : P → A × B)
    (hf : Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f)
    (tag : S → A × B → T) (t : T) :
    Fintype.card {p : P // tag (cell p) (f p) = t} =
      ∑ s, ∑ ab : A × B,
        if tag s ab = t then m s * l s ab.1 * r s ab.2 else 0 := by
  exact prescribed_profile_pushforward cell f _ hf tag t

end MME.DWZPairedTypical

theorem solution
    {P S A B Tag : Type*}
    [Fintype P] [Fintype S] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ)
    (DL DR m : S → ℕ)
    (hl : ∀ s, ∑ a, l s a = DL s) (hr : ∀ s, ∑ b, r s b = DR s)
    (hsize : ∀ s, Fintype.card {p : P // cell p = s} = m s * DL s * DR s) :
    (Fintype.card {f : P → A × B //
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f} =
      ∏ s, Nat.multinomial Finset.univ
        (fun ab : A × B => m s * l s ab.1 * r s ab.2)) ∧
    (∃ f : P → A × B,
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f) ∧
    ∀ f : P → A × B,
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f →
      (∀ s a, MME.RecursiveYZ.count cell (fun p => (f p).1) s a =
        m s * l s a * DR s) ∧
      (∀ s b, MME.RecursiveYZ.count cell (fun p => (f p).2) s b =
        m s * DL s * r s b) ∧
      ∀ (tag : S → A × B → Tag) (t : Tag),
        Fintype.card {p : P // tag (cell p) (f p) = t} =
          ∑ s, ∑ ab : A × B,
            if tag s ab = t then m s * l s ab.1 * r s ab.2 else 0 := by
  refine ⟨MME.DWZPairedTypical.paired_product_profile_card cell l r DL DR m hl hr hsize,
    MME.DWZPairedTypical.paired_product_profile_nonempty cell l r DL DR m hl hr hsize, ?_⟩
  intro f hf
  have hmarg := MME.DWZPairedTypical.paired_product_profile_marginals
    cell l r DL DR m hl hr f hf
  refine ⟨hmarg.1, hmarg.2, ?_⟩
  intro tag t
  exact MME.DWZPairedTypical.paired_product_profile_pushforward cell l r m f hf tag t

