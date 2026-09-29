-- Prove2me | solution 1 for SimpleGraph.OneSumCounterexample.glue_indepNum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:34:53.856466+00:00
-- url     : https://prove2.me/submissions/c4b5eeb2-c359-4bfb-8259-71ab4f4097da

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumIndepRatioCounterexample
open Finset SimpleGraph SimpleGraph.OneSumCounterexample in
theorem solution : Glue.indepNum = 3 := by
  -- away from the cut vertex `0`, each side is a clique
  have hL : ∀ a b : Fin 15, 1 ≤ (a : ℕ) → (a : ℕ) ≤ 7 → 1 ≤ (b : ℕ) → (b : ℕ) ≤ 7 → a ≠ b →
      Glue.Adj a b := by decide
  have hR : ∀ a b : Fin 15, 8 ≤ (a : ℕ) → 8 ≤ (b : ℕ) → a ≠ b → Glue.Adj a b := by decide
  apply le_antisymm
  · -- an independent set meets `{0}`, `{1,…,7}` and `{8,…,14}` in at most one vertex each
    obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := Glue)
    rw [← hs.card_eq]
    have hind := hs.isIndepSet
    have h0 : (s.filter (fun x : Fin 15 => (x : ℕ) = 0)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      exact Fin.ext (ha.2.trans hb.2.symm)
    have h1 : (s.filter (fun x : Fin 15 => 1 ≤ (x : ℕ) ∧ (x : ℕ) ≤ 7)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      by_contra hab
      rw [mem_filter] at ha hb
      exact hind (mem_coe.mpr ha.1) (mem_coe.mpr hb.1) hab
        (hL a b ha.2.1 ha.2.2 hb.2.1 hb.2.2 hab)
    have h2 : (s.filter (fun x : Fin 15 => 8 ≤ (x : ℕ))).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      by_contra hab
      rw [mem_filter] at ha hb
      exact hind (mem_coe.mpr ha.1) (mem_coe.mpr hb.1) hab (hR a b ha.2 hb.2 hab)
    have hsub : s ⊆ s.filter (fun x : Fin 15 => (x : ℕ) = 0)
        ∪ s.filter (fun x : Fin 15 => 1 ≤ (x : ℕ) ∧ (x : ℕ) ≤ 7)
        ∪ s.filter (fun x : Fin 15 => 8 ≤ (x : ℕ)) := by
      intro x hx
      simp only [mem_union, mem_filter, hx, true_and]
      omega
    have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    omega
  · -- `{0, 1, 8}` is independent
    have hI : Glue.IsIndepSet (({0, 1, 8} : Finset (Fin 15)) : Set (Fin 15)) := by
      intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | exact absurd rfl hab | decide
    calc 3 = ({0, 1, 8} : Finset (Fin 15)).card := by decide
      _ ≤ Glue.indepNum := hI.card_le_indepNum
