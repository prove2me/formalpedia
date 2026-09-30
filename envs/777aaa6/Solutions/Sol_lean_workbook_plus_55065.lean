-- Prove2me | solution 1 for lean_workbook_plus_55065
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:23:30.233896+00:00
-- url     : https://prove2.me/submissions/e1afd840-83ea-4a20-8e67-a4a65ffa5016

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

private theorem distinct_repeated_pair (a : ℕ → ℕ) (ha : ∀ n, 0 < a n ∧ a n ≤ 9) :
    ∃ k l : ℕ, k ∈ Finset.Icc 1 98 ∧ l ∈ Finset.Icc 1 98 ∧
      k ≠ l ∧ a k = a l ∧ a (k + 1) = a (l + 1) := by
  let digit (n : ℕ) : Fin 9 := ⟨a n - 1, by have := ha n; omega⟩
  let pair (i : Fin 98) : Fin 9 × Fin 9 := (digit (i.val + 1), digit (i.val + 2))
  have hnot : ¬Function.Injective pair := by
    intro hinj
    have hcard := Fintype.card_le_of_injective pair hinj
    norm_num at hcard
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨i, j, heq, hne⟩ := hnot
  have hf : a (i.val + 1) - 1 = a (j.val + 1) - 1 :=
    congrArg (fun p : Fin 9 × Fin 9 => p.1.val) heq
  have hs : a (i.val + 2) - 1 = a (j.val + 2) - 1 :=
    congrArg (fun p : Fin 9 × Fin 9 => p.2.val) heq
  have hai := ha (i.val + 1)
  have haj := ha (j.val + 1)
  have hbi := ha (i.val + 2)
  have hbj := ha (j.val + 2)
  refine ⟨i.val + 1, j.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, by omega, ?_⟩
  · intro h
    exact hne (Fin.ext (by omega))
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using (show a (i.val + 2) = a (j.val + 2) by omega)

theorem solution (a : ℕ → ℕ) (ha : ∀ n, 0 < a n ∧ a n <= 9)
    (h₁ : ∀ n, a n = 1 → a (n + 1) ≠ 2)
    (h₂ : ∀ n, a n = 3 → a (n + 1) ≠ 4) :
    ∃ k l, k ∈ Finset.Icc 1 98 ∧ l ∈ Finset.Icc 1 98 ∧
      a k = a l ∧ a (k + 1) = a (l + 1) := by
  obtain ⟨k, l, hk, hl, _, heq, heq'⟩ := distinct_repeated_pair a ha
  exact ⟨k, l, hk, hl, heq, heq'⟩
