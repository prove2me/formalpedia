-- Prove2me | solution 1 for LorentzianHardness.quadratic_leaf_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:09:13.686629+00:00
-- url     : https://prove2.me/submissions/610eafa0-ef40-4188-a959-a81ad2eb2d64

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_LorentzianHardness

open Finset BigOperators LorentzianHardness in
theorem solution (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    numberOfQuadraticLeaves n d ≤ n ^ (d - 2) := by
  classical
  -- membership in the multi-index set is just the weight condition
  have hmem : ∀ m (α : Fin n → ℕ), α ∈ multiIndexSet n m ↔ ∑ i, α i = m := by
    intro m α
    simp only [multiIndexSet, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨α i, ?_⟩, rfl⟩, h⟩
      have : α i ≤ ∑ j, α j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
  -- every index of weight `m+1` is an index of weight `m` plus a unit vector
  have hstep : ∀ m, multiIndexCount n (m + 1) ≤ multiIndexCount n m * n := by
    intro m
    have hsub : multiIndexSet n (m + 1) ⊆
        (multiIndexSet n m ×ˢ (Finset.univ : Finset (Fin n))).image
          (fun p => p.1 + Pi.single p.2 1) := by
      intro α hα
      rw [hmem] at hα
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := α) (by omega)
      have hle : ∀ j, (Pi.single i 1 : Fin n → ℕ) j ≤ α j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [Pi.single_eq_same]
          omega
        · simp [Pi.single_eq_of_ne hj]
      refine Finset.mem_image.2 ⟨(α - Pi.single i 1, i), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
        rw [hmem]
        simp only [Pi.sub_apply]
        rw [Finset.sum_tsub_distrib _ (fun j _ => hle j)]
        simp [hα]
      · funext j
        simp only [Pi.add_apply, Pi.sub_apply]
        exact tsub_add_cancel_of_le (hle j)
    calc multiIndexCount n (m + 1) ≤ ((multiIndexSet n m ×ˢ
          (Finset.univ : Finset (Fin n))).image (fun p => p.1 + Pi.single p.2 1)).card :=
          Finset.card_le_card hsub
      _ ≤ (multiIndexSet n m ×ˢ (Finset.univ : Finset (Fin n))).card := Finset.card_image_le
      _ = multiIndexCount n m * n := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; rfl
  have hzero : multiIndexCount n 0 ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [hmem] at ha hb
    have ha' := (Finset.sum_eq_zero_iff.1 ha)
    have hb' := (Finset.sum_eq_zero_iff.1 hb)
    funext i
    rw [ha' i (Finset.mem_univ i), hb' i (Finset.mem_univ i)]
  have hall : ∀ m, multiIndexCount n m ≤ n ^ m := by
    intro m
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      calc multiIndexCount n (m + 1) ≤ multiIndexCount n m * n := hstep m
        _ ≤ n ^ m * n := Nat.mul_le_mul_right _ ih
        _ = n ^ (m + 1) := (pow_succ n m).symm
  unfold numberOfQuadraticLeaves
  rw [if_neg (by omega)]
  exact hall (d - 2)
