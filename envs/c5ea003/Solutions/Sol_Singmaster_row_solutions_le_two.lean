-- Prove2me | solution 1 for Singmaster.row_solutions_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:08:50.969105+00:00
-- url     : https://prove2.me/submissions/981ccf1d-c9c9-48c2-af7d-7d7c75c27a6b

import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterRefinements
open Singmaster in
theorem solution (n t : ℕ) : (rowOcc n t).card ≤ 2 := by
  -- `choose n` strictly increases below the middle of the row
  have hstep : ∀ k, 2 * k + 1 < n → n.choose k < n.choose (k + 1) := by
    intro k hk
    have h1 := Nat.choose_succ_right_eq n k
    have hpos : 0 < n.choose k := Nat.choose_pos (by omega)
    by_contra hle
    push Not at hle
    have h2 : n.choose k * (n - k) ≤ n.choose k * (k + 1) := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ hle
    have h3 := Nat.le_of_mul_le_mul_left h2 hpos
    omega
  have hmono : ∀ a b, a < b → 2 * b ≤ n → n.choose a < n.choose b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
      · exact (ih h (by omega)).trans (hstep b (by omega))
      · subst h
        exact hstep a (by omega)
  rcases (rowOcc n t).eq_empty_or_nonempty with he | ⟨k0, hk0⟩
  · rw [he]
    simp
  have hmem : ∀ k ∈ rowOcc n t, k ≤ n ∧ n.choose k = t := by
    intro k hk
    simp only [rowOcc, Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨by omega, hk.2⟩
  -- by symmetry each value in the row is seen at `m = min k (n - k)`, and `m` is unique
  have hmin : ∀ k, k ≤ n → n.choose (min k (n - k)) = n.choose k := by
    intro k hk
    rcases le_total k (n - k) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Nat.choose_symm hk]
  have hkey : ∀ k ∈ rowOcc n t, min k (n - k) = min k0 (n - k0) := by
    intro k hk
    obtain ⟨hkn, hkt⟩ := hmem k hk
    obtain ⟨hk0n, hk0t⟩ := hmem k0 hk0
    have heq : n.choose (min k (n - k)) = n.choose (min k0 (n - k0)) := by
      rw [hmin k hkn, hmin k0 hk0n, hkt, hk0t]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd heq (ne_of_lt (hmono _ _ h (by omega)))
    · exact absurd heq (ne_of_gt (hmono _ _ h (by omega)))
  have hsub : rowOcc n t ⊆ {min k0 (n - k0), n - min k0 (n - k0)} := by
    intro k hk
    have h1 := hkey k hk
    have h2 := (hmem k hk).1
    rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_two
