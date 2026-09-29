-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trains
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:33:27.222825+00:00
-- url     : https://prove2.me/submissions/0158a2b8-19bd-4dcb-92a5-db575607f71a

/-
# `Catalog.Probability.NeuralCoding.Temporal.card_trains`
Target `00bd2642` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`trains` is defined by the refractory recursion
    trains 0       = {[]}
    trains 1       = {[false], [true]}
    trains (n + 2) = image (false :: ·) (trains (n+1))  ∪  image (true :: false :: ·) (trains n)
which is Fibonacci's recursion once the two branches are shown disjoint with injective maps:
  * the two images are DISJOINT because members of the first begin with `false` and members of the
    second begin with `true`;
  * `fun l => false :: l` and `fun l => true :: false :: l` are INJECTIVE (cons is injective).
Hence card (trains (n+2)) = card (trains (n+1)) + card (trains n), and with the base cases
card = 1 = fib 2 and card = 2 = fib 3 the claim card (trains n) = fib (n+2) follows by two-step
induction.
-/
import Mathlib
import Definitions.Def_Probability_RefractorySpikeTrains

set_option autoImplicit false

open Finset Catalog.Probability.NeuralCoding.Temporal in
/-- **The target, verbatim.** -/
theorem solution : ∀ n : ℕ, (trains n).card = Nat.fib (n + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [trains]
    | 1 => decide
    | (m + 2) =>
      have hinj1 : Function.Injective (fun l : List Bool => false :: l) := by
        intro a b h; simpa using h
      have hinj2 : Function.Injective (fun l : List Bool => true :: false :: l) := by
        intro a b h; simpa using h
      have hdisj : Disjoint
          ((trains (m + 1)).image (fun l : List Bool => false :: l))
          ((trains m).image (fun l : List Bool => true :: false :: l)) := by
        rw [Finset.disjoint_left]
        rintro x hx hy
        simp only [Finset.mem_image] at hx hy
        obtain ⟨a, _, rfl⟩ := hx
        obtain ⟨b, _, hb⟩ := hy
        exact absurd hb (by simp)
      have hcard : (trains (m + 2)).card
          = (trains (m + 1)).card + (trains m).card := by
        show ((trains (m + 1)).image (fun l : List Bool => false :: l) ∪
              (trains m).image (fun l : List Bool => true :: false :: l)).card = _
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ hinj1,
            Finset.card_image_of_injective _ hinj2]
      rw [hcard, ih (m + 1) (by omega), ih m (by omega)]
      have : m + 2 + 2 = (m + 2) + 2 := rfl
      simp [Nat.fib_add_two]
      ring
