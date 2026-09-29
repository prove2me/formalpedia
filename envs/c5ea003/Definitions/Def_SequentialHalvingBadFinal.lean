-- Prove2me | Definitions.Def_SequentialHalvingBadFinal
-- name    : SequentialHalvingBadFinal
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-02T16:37:14.882366+00:00
-- url     : https://prove2.me/theorems/e32a906b-02f8-4128-979c-da879c0be568
-- title:
--   Sequential Halving bad-final and last-optimal-elimination events
-- statement:
--   `IsSeqHalvingBadFinalRun` records a complete Sequential Halving active-set chain that starts with at least one optimal arm and ends with no optimal arm. `IsSeqHalvingLastOptimalEliminationAt` records the phase-local transition at which the active set changes from containing an optimal arm to containing only suboptimal arms.
--
--   These predicates isolate the correct failure events when a bandit may have multiple optimal arms: eliminating one particular optimal arm is harmless if another optimal arm survives, whereas eliminating the last optimal arm is the event relevant to misidentification.
--
--   **Formalization Note** Optimality is expressed by zero gap and suboptimality by strictly positive gap.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Algorithm 22 and Exercise 33.8(c)–(f), printed pp. 412–413 and 419–420. The last-optimal formulation makes the proof valid with multiple optimal arms.

import Definitions.Def_SequentialHalving

open Finset

namespace BanditAlgorithm

/-- A complete Sequential Halving active-set chain which starts with at least
one optimal arm and ends with no optimal arm. -/
def IsSeqHalvingBadFinalRun (k n : ℕ) (ν : StochasticBandit k)
    (h : BanditHistory k n) : Prop :=
  ∃ A : ℕ → Finset (Fin k),
    A 0 = Finset.univ ∧
    (∀ s < Nat.clog 2 k,
      A (s + 1) ⊆ A s ∧
      (A (s + 1)).card = ((A s).card + 1) / 2 ∧
      (∀ i ∈ A (s + 1), ∀ j ∈ A s \ A (s + 1),
        seqHalvingPhaseMean h s j ≤ seqHalvingPhaseMean h s i) ∧
      (∀ t ∈ seqHalvingPhase k n s, (h t).1 ∈ A s) ∧
      (∀ i ∈ A s,
        ((seqHalvingPhase k n s).filter (fun t ↦ (h t).1 = i)).card =
          seqHalvingPulls k n s)) ∧
    (∃ i ∈ A 0, banditGap ν i = 0) ∧
    (∀ i ∈ A (Nat.clog 2 k), 0 < banditGap ν i)

/-- A complete Sequential Halving active-set chain in which phase `ℓ`
eliminates every optimal arm that was still active. -/
def IsSeqHalvingLastOptimalEliminationAt (k n : ℕ) (ν : StochasticBandit k)
    (h : BanditHistory k n) (ℓ : ℕ) : Prop :=
  ∃ A : ℕ → Finset (Fin k),
    A 0 = Finset.univ ∧
    (∀ s < Nat.clog 2 k,
      A (s + 1) ⊆ A s ∧
      (A (s + 1)).card = ((A s).card + 1) / 2 ∧
      (∀ i ∈ A (s + 1), ∀ j ∈ A s \ A (s + 1),
        seqHalvingPhaseMean h s j ≤ seqHalvingPhaseMean h s i) ∧
      (∀ t ∈ seqHalvingPhase k n s, (h t).1 ∈ A s) ∧
      (∀ i ∈ A s,
        ((seqHalvingPhase k n s).filter (fun t ↦ (h t).1 = i)).card =
          seqHalvingPulls k n s)) ∧
    (∃ i ∈ A ℓ, banditGap ν i = 0) ∧
    (∀ i ∈ A (ℓ + 1), 0 < banditGap ν i)

end BanditAlgorithm


