-- Prove2me | solution 1 for mme_dwz_paired_exact_typical_useful_word_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:20:05.14899+00:00
-- url     : https://prove2.me/submissions/5ba20aee-6455-47de-b78f-7ce6058f5f48

import Theorems.Thm_mme_dwz_paired_product_type_card_and_marginals
import Theorems.Thm_mme_prescribed_cell_histogram_card
import Theorems.Thm_mme_dwz_paired_exact_typical_useful_log_rate
import Mathlib.Tactic

open BigOperators Filter MME.RecursiveYZ
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.DWZC1PairedTypicalWords

def childCell {P S : Type*} (sigma : S ≃ S) (cell : P → S) (v : P × Fin 2) : S :=
  if v.2 = 0 then cell v.1 else sigma (cell v.1)

def unfoldPair {P A : Type*} (f : P → A × A) (v : P × Fin 2) : A :=
  if v.2 = 0 then (f v.1).1 else (f v.1).2

def foldPair {P A : Type*} (w : P × Fin 2 → A) (v : P) : A × A :=
  (w (v, 0), w (v, 1))

def pairWordEquiv {P A : Type*} : (P → A × A) ≃ (P × Fin 2 → A) where
  toFun := unfoldPair
  invFun := foldPair
  left_inv := by intro f; funext v; simp [foldPair, unfoldPair]
  right_inv := by
    intro w
    funext ⟨v, h⟩
    fin_cases h <;> simp [foldPair, unfoldPair]

theorem child_count_unfold
    {P S A : Type*} [Fintype P]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (cell : P → S) (f : P → A × A) (s : S) (a : A) :
    count (childCell sigma cell) (unfoldPair f) s a =
      count cell (fun v ↦ (f v).1) s a +
        count cell (fun v ↦ (f v).2) (sigma s) a := by
  have heq (v : P) : sigma (cell v) = s ↔ cell v = sigma s := by
    constructor
    · intro h
      simpa only [hsigma] using congrArg sigma h
    · intro h
      rw [h, hsigma]
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, Fin.sum_univ_two, childCell, unfoldPair]
  simp only [Fin.reduceEq, if_true, if_false, heq, Finset.sum_add_distrib]

theorem exact_joint_implies_merged_useful
    {P S A : Type*} [Fintype P] [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (cell : P → S) (p : S → A → ℕ) (D : ℕ)
    (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) (t : ℕ)
    (hsize : ∀ s, Fintype.card {v : P // cell v = s} = t * k s * D * D)
    (f : P → A × A)
    (hf : Useful cell (fun s (ab : A × A) ↦
      t * k s * p s ab.1 * p (sigma s) ab.2) f) :
    Useful (childCell sigma cell)
      (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) (unfoldPair f) := by
  have h := (mme_dwz_paired_product_type_card_and_marginals
    (Tag := Unit) cell p (fun s ↦ p (sigma s))
    (fun _ ↦ D) (fun _ ↦ D) (fun s ↦ t * k s) hp (fun s ↦ hp (sigma s))
    hsize).2.2 f hf
  intro s a
  rw [child_count_unfold sigma hsigma cell f s a, h.1, h.2.1, hsigma]
  ring

theorem useful_count_sum
    {P S A : Type*} [Fintype P] [Fintype A]
    (cell : P → S) (mu : S → A → ℕ) (f : P → A)
    (hf : Useful cell mu f) (s : S) :
    (∑ a, mu s a) = Fintype.card {v : P // cell v = s} := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun v : P ↦ cell v = s))
    (t := Finset.univ) (f := f) (fun _ _ ↦ Finset.mem_univ _)
  rw [Fintype.card_subtype]
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hf s a]
  simp only [count, Finset.filter_filter]

/-- Exact paired profiles, expressed as a subset of actual merged-useful
words on both child positions of every parent position. -/
def JointTypical
    {P S A : Type*} [Fintype P]
    (sigma : S ≃ S) (cell : P → S) (p : S → A → ℕ)
    (D : ℕ) (k : S → ℕ) (t : ℕ) (w : P × Fin 2 → A) : Prop :=
  Useful (childCell sigma cell)
    (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) w ∧
  Useful cell (fun s (ab : A × A) ↦
    t * k s * p s ab.1 * p (sigma s) ab.2) (foldPair w)

theorem joint_typical_card_and_pushforward
    {P S A Tag : Type*} [Fintype P] [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (cell : P → S) (p : S → A → ℕ) (D : ℕ)
    (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) (t : ℕ)
    (hsize : ∀ s, Fintype.card {v : P // cell v = s} = t * k s * D * D) :
    Fintype.card {w : P × Fin 2 → A // JointTypical sigma cell p D k t w} =
      ∏ s, Nat.multinomial Finset.univ
        (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) ∧
    Fintype.card {w : P × Fin 2 → A // Useful (childCell sigma cell)
      (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) w} =
      ∏ s, Nat.multinomial Finset.univ
        (fun a ↦ t * D * (k s + k (sigma s)) * p s a) ∧
    ∀ w : P × Fin 2 → A, JointTypical sigma cell p D k t w →
      ∀ (tag : S → A × A → Tag) (z : Tag),
        Fintype.card {v : P // tag (cell v) (foldPair w v) = z} =
          ∑ s, ∑ ab : A × A, if tag s ab = z then
            t * k s * p s ab.1 * p (sigma s) ab.2 else 0 := by
  have h := mme_dwz_paired_product_type_card_and_marginals
    (Tag := Tag) cell p (fun s ↦ p (sigma s))
    (fun _ ↦ D) (fun _ ↦ D) (fun s ↦ t * k s) hp (fun s ↦ hp (sigma s)) hsize
  constructor
  · have he : {f : P → A × A // Useful cell (fun s ab ↦
        t * k s * p s ab.1 * p (sigma s) ab.2) f} ≃
        {w : P × Fin 2 → A // JointTypical sigma cell p D k t w} :=
      { toFun := fun f ↦ ⟨unfoldPair f.val,
          exact_joint_implies_merged_useful sigma hsigma cell p D hp k t hsize f.val f.property,
          by
            rw [show foldPair (unfoldPair f.val) = f.val from pairWordEquiv.left_inv f.val]
            exact f.property⟩
        invFun := fun w ↦ ⟨foldPair w.val, w.property.2⟩
        left_inv := by intro f; apply Subtype.ext; exact pairWordEquiv.left_inv f.val
        right_inv := by intro w; apply Subtype.ext; exact pairWordEquiv.right_inv w.val }
    exact (Fintype.card_congr he).symm.trans h.1
  constructor
  · obtain ⟨f, hf⟩ := h.2.1
    have hu := exact_joint_implies_merged_useful sigma hsigma cell p D hp k t hsize f hf
    have hm := useful_count_sum (childCell sigma cell)
      (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) (unfoldPair f) hu
    have hcard := mme_prescribed_cell_histogram_card (childCell sigma cell)
      (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) hm
    have hcard' : Fintype.card {w : P × Fin 2 → A // Useful (childCell sigma cell)
        (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) w} =
        ∏ s, (Fintype.card {v : P × Fin 2 // childCell sigma cell v = s}).factorial /
          ∏ a, (t * D * (k s + k (sigma s)) * p s a).factorial := by
      convert hcard using 1
      exact congrArg (fun h ↦ @Fintype.card _ h) (Subsingleton.elim _ _)
    refine hcard'.trans ?_
    apply Finset.prod_congr rfl
    intro s _
    rw [Nat.multinomial, hm s]
  · intro w hw tag z
    exact (h.2.2 (foldPair w) hw.2).2.2 tag z

theorem joint_typical_nonempty
    {P S A : Type*} [Fintype P] [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (cell : P → S) (p : S → A → ℕ) (D : ℕ)
    (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) (t : ℕ)
    (hsize : ∀ s, Fintype.card {v : P // cell v = s} = t * k s * D * D) :
    ∃ w : P × Fin 2 → A, JointTypical sigma cell p D k t w := by
  have h := (joint_typical_card_and_pushforward (Tag := Unit)
    sigma hsigma cell p D hp k t hsize).1
  have hpos : 0 < Fintype.card
      {w : P × Fin 2 → A // JointTypical sigma cell p D k t w} := by
    rw [h]
    exact Finset.prod_pos (fun s _ ↦ Nat.multinomial_pos _ _)
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨w.val, w.property⟩

/-- The analytic paired-type rate is realized by an actual subset of useful
words on the two child positions, for any family of paired position sets. -/
theorem eventually_actual_joint_typical_fraction
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ)
    (P : ℕ → Type*) [∀ t, Fintype (P t)] (cell : ∀ t, P t → S)
    (hsize : ∀ t s, Fintype.card {v : P t // cell t v = s} = t * k s * D * D)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) *
        (Fintype.card {w : P t × Fin 2 → A // Useful (childCell sigma (cell t))
          (fun s a ↦ t * D * (k s + k (sigma s)) * p s a) w} : ℝ) ≤
      (Fintype.card {w : P t × Fin 2 → A //
        JointTypical sigma (cell t) p D k t w} : ℝ) := by
  filter_upwards [(mme_dwz_paired_exact_typical_useful_log_rate
    sigma hsigma p D hp k).2 eps heps] with t ht
  have h := joint_typical_card_and_pushforward (Tag := Unit)
    sigma hsigma (cell t) p D hp k t (hsize t)
  rw [h.1, h.2.1, Nat.cast_prod, Nat.cast_prod]
  exact ht

end MME.DWZC1PairedTypicalWords

theorem solution
    {S A Tag : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ)
    (P : ℕ → Type*) [∀ t, Fintype (P t)] (cell : ∀ t, P t → S)
    (hsize : ∀ t s, Fintype.card {v : P t // cell t v = s} = t * k s * D * D) :
    let child : ∀ t, P t × Fin 2 → S := fun t v ↦
      if v.2 = 0 then cell t v.1 else sigma (cell t v.1)
    let joint : ℕ → S → A × A → ℕ := fun t s ab ↦
      t * k s * p s ab.1 * p (sigma s) ab.2
    let merged : ℕ → S → A → ℕ := fun t s a ↦
      t * D * (k s + k (sigma s)) * p s a
    let typical : ∀ t, (P t × Fin 2 → A) → Prop := fun t w ↦
      Useful (child t) (merged t) w ∧
      Useful (cell t) (joint t) (fun v ↦ (w (v, 0), w (v, 1)))
    (∀ t,
      (∃ w : P t × Fin 2 → A, typical t w) ∧
      Fintype.card {w : P t × Fin 2 → A // typical t w} =
        ∏ s, Nat.multinomial Finset.univ (joint t s) ∧
      Fintype.card {w : P t × Fin 2 → A // Useful (child t) (merged t) w} =
        ∏ s, Nat.multinomial Finset.univ (merged t s) ∧
      ∀ w : P t × Fin 2 → A, typical t w →
        ∀ (tag : S → A × A → Tag) (z : Tag),
          Fintype.card {v : P t // tag (cell t v) (w (v, 0), w (v, 1)) = z} =
            ∑ s, ∑ ab : A × A, if tag s ab = z then joint t s ab else 0) ∧
    ∀ eps : ℝ, 0 < eps → ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) *
        (Fintype.card {w : P t × Fin 2 → A // Useful (child t) (merged t) w} : ℝ) ≤
      (Fintype.card {w : P t × Fin 2 → A // typical t w} : ℝ) := by
  dsimp only
  constructor
  · intro t
    have h := MME.DWZC1PairedTypicalWords.joint_typical_card_and_pushforward
      (Tag := Tag) sigma hsigma (cell t) p D hp k t (hsize t)
    refine ⟨MME.DWZC1PairedTypicalWords.joint_typical_nonempty
      sigma hsigma (cell t) p D hp k t (hsize t), ?_⟩
    simpa only [Fintype.card_eq_nat_card] using h
  · intro eps heps
    simpa only [Fintype.card_eq_nat_card] using
      MME.DWZC1PairedTypicalWords.eventually_actual_joint_typical_fraction
        sigma hsigma p D hp k P cell hsize eps heps
