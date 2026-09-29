-- Prove2me | solution 1 for TFoldSumsetAvoidance.sumsetList_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:12:35.195812+00:00
-- url     : https://prove2.me/submissions/a8d301f9-ec3a-47c4-8459-2953cb09bece

import Mathlib
import Definitions.Def_Logic_PosetTheory_TFoldSumsetAvoidance
open Pointwise TFoldSumsetAvoidance in
theorem solution (l : List (Finset ℤ)) (h : ∀ A ∈ l, A.Nonempty) :
    (l.map Finset.card).sum + 1 ≤ (sumsetList l).card + l.length := by
  -- the iterated sumset of nonempty sets is nonempty
  have hne : ∀ M : List (Finset ℤ), (∀ B ∈ M, B.Nonempty) → (sumsetList M).Nonempty := by
    intro M hM
    induction M with
    | nil => simp [sumsetList]
    | cons B M ihB =>
      have hB : B.Nonempty := hM B List.mem_cons_self
      have hrest := ihB (fun C hC => hM C (List.mem_cons_of_mem B hC))
      exact hB.add hrest
  induction l with
  | nil => simp [sumsetList]
  | cons A l ih =>
    have hA : A.Nonempty := h A List.mem_cons_self
    have hl : ∀ B ∈ l, B.Nonempty := fun B hB => h B (List.mem_cons_of_mem A hB)
    -- Cauchy–Davenport over `ℤ`: `|A + S| ≥ |A| + |S| - 1`
    have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hA (hne l hl)
    have hIH := ih hl
    have hA1 : 1 ≤ A.card := hA.card_pos
    have hunfold : sumsetList (A :: l) = A + sumsetList l := rfl
    rw [hunfold, List.map_cons, List.sum_cons, List.length_cons]
    omega
