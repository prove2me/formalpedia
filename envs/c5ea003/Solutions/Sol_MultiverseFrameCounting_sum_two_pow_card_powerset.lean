-- Prove2me | solution 1 for MultiverseFrameCounting.sum_two_pow_card_powerset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:38:19.438054+00:00
-- url     : https://prove2.me/submissions/2451f1c7-0b9d-44bc-b978-4fdb67fbcb13

-- Sol generated from Logic/Multiverse/FrameCounting.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_FrameCounting
/-
# Counting the Finite Control Frames

A combinatorial companion to `Catalog/Logic/Multiverse/BooleanValuedRealization.lean`.

The finite pre-Boolean forcing frames used for the countermodels are assembled from
`n` independent buttons and `m` independent switches.  We compute their size
exactly:

* `sum_two_pow_card_powerset` — `∑_{t ⊆ s} 2^|t| = 3^|s|`, proved by induction on
  `s` (the enumerative heart: each element is either outside `t`, inside `t` but
  outside the ambient set, or in both);
* `card_cacc_pairs` — the frame with `n` buttons and `m` switches has exactly
  `3^n · 4^m` accessibility pairs, and (`card_worlds`) `2^(n+m)` worlds.

The count `3^n · 4^m` is exactly what an independent enumeration of the frames
produces (see `ComputationalEvidence.md`), and it exhibits the accessibility
relation as a *product* of `n` three-element button orders with `m` complete
two-element switch relations — the combinatorial form of the statement that buttons
and switches act independently.
-/

open MultiverseFrameCounting

open BooleanValuedRealization Finset

variable {α : Type*} [DecidableEq α]







open MultiverseFrameCounting in
theorem solution(s : Finset α) :
    ∑ t ∈ s.powerset, 2 ^ t.card = 3 ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha, ih, Finset.card_insert_of_notMem ha]
      have h2 : ∑ t ∈ s.powerset, 2 ^ (insert a t).card
          = ∑ t ∈ s.powerset, 2 * 2 ^ t.card := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hat : a ∉ t := fun h => ha (Finset.mem_powerset.1 ht h)
        rw [Finset.card_insert_of_notMem hat, pow_succ, mul_comm]
      rw [h2, ← Finset.mul_sum, ih]
      ring
