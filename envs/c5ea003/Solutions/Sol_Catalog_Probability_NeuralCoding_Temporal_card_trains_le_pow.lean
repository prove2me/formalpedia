-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trains_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:24:33.312503+00:00
-- url     : https://prove2.me/submissions/0d026e9f-a15a-4ec3-9181-345a09740978

import Definitions.Def_Probability_RefractorySpikeTrains

open Catalog.Probability.NeuralCoding.Temporal Finset

open Catalog.Probability.NeuralCoding.Temporal Finset in
/-- **Refractory spike trains of length `5m` number at most `16^m`.** -/
theorem solution : ∀ m : ℕ, (trains (5 * m)).card ≤ 16 ^ m := by
  have hcard : ∀ n, (trains n).card = Nat.fib (n + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => rfl
      | 1, _ => rfl
      | k + 2, ih =>
        rw [trains, Finset.card_union_of_disjoint,
          Finset.card_image_of_injective _ List.cons_injective,
          Finset.card_image_of_injective _ (fun a b h => List.cons_injective (List.cons_injective h)),
          ih (k + 1) (by omega), ih k (by omega)]
        · have f : Nat.fib (k + 2 + 2) = Nat.fib (k + 2) + Nat.fib (k + 2 + 1) := Nat.fib_add_two
          have e1 : k + 1 + 2 = k + 2 + 1 := by omega
          rw [e1, f]
          omega
        · rw [Finset.disjoint_left]
          intro l hl hl'
          simp only [Finset.mem_image] at hl hl'
          obtain ⟨a, -, rfl⟩ := hl
          obtain ⟨b, -, hb⟩ := hl'
          simp at hb
  have hgrow : ∀ m, Nat.fib (5 * m + 2) ≤ 16 ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have e : 5 * (m + 1) + 2 = (5 * m + 2) + 5 := by ring
      rw [e, pow_succ]
      generalize ha : 5 * m + 2 = a at ih ⊢
      have f2 : Nat.fib (a + 2) = Nat.fib a + Nat.fib (a + 1) := Nat.fib_add_two
      have f3 : Nat.fib (a + 3) = Nat.fib (a + 1) + Nat.fib (a + 2) := Nat.fib_add_two
      have f4 : Nat.fib (a + 4) = Nat.fib (a + 2) + Nat.fib (a + 3) := Nat.fib_add_two
      have f5 : Nat.fib (a + 5) = Nat.fib (a + 3) + Nat.fib (a + 4) := Nat.fib_add_two
      have hle : Nat.fib (a + 1) ≤ 2 * Nat.fib a := by
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        show Nat.fib (b + 2) ≤ 2 * Nat.fib (b + 1)
        have g1 : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
        have g2 : Nat.fib b ≤ Nat.fib (b + 1) := Nat.fib_le_fib_succ
        omega
      omega
  intro m
  rw [hcard]
  exact hgrow m
