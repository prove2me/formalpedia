-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.mem_trains_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:00:23.424308+00:00
-- url     : https://prove2.me/submissions/7da4d5c2-79c0-4c9a-8f05-2ada36f506bd

-- Sol generated from Probability/RefractorySpikeTrains.lean
import Mathlib
import Definitions.Def_Probability_RefractorySpikeTrains
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Temporal neural codes: finite-window capacity under a refractory period

`Catalog/Novelty/NeuralCoding.lean` codes a concept by a single Boolean pattern
across neurons.  A *temporal* code instead uses the spike train of one neuron
across a window of `T` discrete time bins.  Biophysics forbids two spikes in
consecutive bins (the absolute refractory period), so the admissible spike
trains are exactly the binary words of length `T` with no two adjacent `true`s.

## Results

1. `trains` — the finset of admissible spike trains in a window of `T` bins,
   defined by the refractory recursion, and `solution`, which proves that
   this finset is *exactly* the set of length-`T` words with no two adjacent
   spikes.
2. `card_trains` — **finite-window capacity**: a refractory neuron has exactly
   `fib (T + 2)` distinguishable spike trains in `T` bins.
3. `card_trains_lt_two_pow` — the refractory constraint is a strict loss:
   capacity is `< 2 ^ T` for `T ≥ 2`.
4. `fib_five_step` / `card_trains_le_pow` — a quantitative rate bound:
   the capacity of a `5m`-bin window is at most `16 ^ m`, i.e. the temporal
   code carries at most `4/5` of a bit per time bin.
5. `temporal_rate_le` — the same statement in bits.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Finset


instance : DecidableRel NoAdj := fun a b => by unfold NoAdj; infer_instance

theorem isChain_tail {a : Bool} {m : List Bool} (h : List.IsChain NoAdj (a :: m)) :
    List.IsChain NoAdj m := by
  match m with
  | [] => exact List.isChain_nil
  | (b :: t) => exact (List.isChain_cons_cons.mp h).2

theorem isChain_false_cons {m : List Bool} (h : List.IsChain NoAdj m) :
    List.IsChain NoAdj (false :: m) := by
  match m with
  | [] => exact List.isChain_singleton _
  | (b :: t) => exact List.isChain_cons_cons.mpr ⟨by simp [NoAdj], h⟩









open Catalog.Probability.NeuralCoding.Temporal in
theorem solution: ∀ (n : ℕ) (l : List Bool),
    l ∈ trains n ↔ l.length = n ∧ l.IsChain NoAdj
  | 0, l => by
      constructor
      · intro h
        simp only [trains, Finset.mem_singleton] at h
        subst h
        exact ⟨rfl, List.isChain_nil⟩
      · rintro ⟨hlen, -⟩
        have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
        simp [trains, hl]
  | 1, l => by
      match l with
      | [] => simp [trains]
      | [a] =>
          constructor
          · intro _; exact ⟨rfl, List.isChain_singleton a⟩
          · intro _; cases a <;> simp [trains]
      | (a :: b :: t) =>
          constructor
          · intro h; simp [trains] at h
          · rintro ⟨hlen, -⟩; simp at hlen
  | (n + 2), l => by
      constructor
      · intro h
        simp only [trains, Finset.mem_union, Finset.mem_image] at h
        rcases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
        · have hIH := (solution (n + 1) m).mp hm
          exact ⟨by simp [hIH.1], isChain_false_cons hIH.2⟩
        · have hIH := (solution n m).mp hm
          refine ⟨by simp [hIH.1], ?_⟩
          exact List.isChain_cons_cons.mpr ⟨by simp [NoAdj], isChain_false_cons hIH.2⟩
      · rintro ⟨hlen, hch⟩
        match l with
        | [] => simp at hlen
        | [a] => simp at hlen
        | (a :: b :: t) =>
            simp only [trains, Finset.mem_union, Finset.mem_image]
            rw [List.isChain_cons_cons] at hch
            cases a with
            | false =>
                left
                exact ⟨b :: t, (solution (n + 1) (b :: t)).mpr
                  ⟨by simpa using hlen, hch.2⟩, rfl⟩
            | true =>
                have hb : b = false := by
                  by_contra hb
                  exact hch.1 ⟨rfl, by simpa using hb⟩
                subst hb
                right
                exact ⟨t, (solution n t).mpr
                  ⟨by simpa using hlen, isChain_tail hch.2⟩, rfl⟩
