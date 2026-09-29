-- Prove2me | solution 2 for Singmaster.two_mul_rows_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:03:11.959062+00:00
-- url     : https://prove2.me/submissions/e894d7af-be20-4ba0-aa02-7b8ca7084c32

import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterRefinements
open Singmaster in
theorem solution {t : ℕ} (ht : 2 ≤ t) : mult t ≤ 2 * (rowsOf t).card := by
  -- a value occurs at most twice in any row of Pascal's triangle
  have hrow : ∀ n t : ℕ, (rowOcc n t).card ≤ 2 := by
    intro n t
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
  -- split the occurrences of `t` by row
  unfold mult
  let emb : ℕ → ℕ ↪ ℕ × ℕ := fun n => ⟨fun k => (n, k), fun a b h => by simpa using h⟩
  have hsub : occ t ⊆ (rowsOf t).biUnion (fun n => (rowOcc n t).map (emb n)) := by
    rintro ⟨n, k⟩ hp
    rw [Finset.mem_biUnion]
    refine ⟨n, Finset.mem_image.mpr ⟨(n, k), hp, rfl⟩, ?_⟩
    rw [Finset.mem_map]
    refine ⟨k, ?_, rfl⟩
    simp only [occ, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [rowOcc, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2.2⟩
  calc (occ t).card ≤ ((rowsOf t).biUnion (fun n => (rowOcc n t).map (emb n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ n ∈ rowsOf t, ((rowOcc n t).map (emb n)).card := Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ rowsOf t, 2 := Finset.sum_le_sum fun n _ => by
        rw [Finset.card_map]
        exact hrow n t
    _ = 2 * (rowsOf t).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
