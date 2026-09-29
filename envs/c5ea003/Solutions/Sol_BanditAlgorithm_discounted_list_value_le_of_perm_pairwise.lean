-- Prove2me | solution 1 for BanditAlgorithm.discounted_list_value_le_of_perm_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:40:19.018984+00:00
-- url     : https://prove2.me/submissions/3ec12bf6-5352-4c74-9ff9-caaa0924d2db

import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

private def discountedListValue (α : ℝ) (xs : List ℝ) : ℝ :=
  xs.foldr (fun z acc ↦ z + α * acc) 0

private lemma move_max_to_front
    {α b : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ {l r : List ℝ}, (∀ z ∈ l, z ≤ b) →
      discountedListValue α (l ++ b :: r) ≤
        discountedListValue α (b :: (l ++ r)) := by
  intro l
  induction l with
  | nil =>
      intro r hl
      simp [discountedListValue]
  | cons z l ih =>
      intro r hl
      have hzb : z ≤ b := hl z (by simp)
      have htail : ∀ w ∈ l, w ≤ b := by
        intro w hw
        exact hl w (by simp [hw])
      have hmove := ih (r := r) htail
      simp only [List.cons_append, discountedListValue]
      calc
        z + α * discountedListValue α (l ++ b :: r)
            ≤ z + α * discountedListValue α (b :: (l ++ r)) := by
              gcongr
        _ = z + α * b + α ^ 2 * discountedListValue α (l ++ r) := by
              simp [discountedListValue]
              ring
        _ ≤ b + α * z + α ^ 2 * discountedListValue α (l ++ r) := by
              have : z + α * b ≤ b + α * z := by
                nlinarith
              linarith
        _ = b + α * discountedListValue α (z :: (l ++ r)) := by
              simp [discountedListValue]
              ring

theorem solution
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {xs ys : List ℝ} (hperm : xs.Perm ys)
    (hsorted : ys.Pairwise (· ≥ ·)) :
    xs.foldr (fun z acc ↦ z + α * acc) 0 ≤
      ys.foldr (fun z acc ↦ z + α * acc) 0 := by
  change discountedListValue α xs ≤ discountedListValue α ys
  induction ys generalizing xs with
  | nil =>
      have : xs = [] := List.Perm.eq_nil hperm
      simp [this, discountedListValue]
  | cons b ys ih =>
      have hbmem : b ∈ xs := hperm.mem_iff.mpr (by simp)
      obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hbmem
      have htailperm : (l ++ r).Perm ys := by
        have hp : (l ++ b :: r).Perm (b :: (l ++ r)) := by
          exact List.perm_middle
        exact List.Perm.cons_inv (hp.symm.trans hperm)
      have hb : ∀ z ∈ l, z ≤ b := by
        intro z hz
        have hzmem : z ∈ b :: ys := hperm.mem_iff.mp (by simp [hz])
        simp only [List.mem_cons] at hzmem
        rcases hzmem with hzb | hzys
        · simpa [hzb]
        · exact (List.pairwise_cons.mp hsorted).1 z hzys
      calc
        discountedListValue α (l ++ b :: r)
            ≤ discountedListValue α (b :: (l ++ r)) :=
              move_max_to_front hα0 hα1 hb
        _ ≤ discountedListValue α (b :: ys) := by
              simp only [discountedListValue, List.foldr_cons]
              gcongr
              exact ih htailperm hsorted.tail
