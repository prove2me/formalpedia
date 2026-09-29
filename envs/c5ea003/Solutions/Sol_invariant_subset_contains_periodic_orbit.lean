-- Prove2me | solution 1 for invariant_subset_contains_periodic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:17.439044+00:00
-- url     : https://prove2.me/submissions/1ea6ea65-c213-45bf-97ac-df57bb02aef3

-- Sol generated from Bridges/ProofStoneCechDynamics.lean
import Mathlib
import Definitions.Def_Bridges_ProofStoneCechDynamics
/-
# Algebraic–EML Stone–Čech Completion for Proof-Semiring Dynamics and Fixed-Point Capacity

Bridge: connects spectral algebraic semantics to certified robustness via closure
dynamics and compactness methods.

## Overview

This file builds a compact spectral completion framework for proof-semiring dynamics,
proving fixed-point capacity theorems: every self-map on a finite type admits periodic
orbits (certified recurrent states), invariant regions persist under iteration, and
closure drift grows at most linearly.

## Main results

* `exists_periodic_point_finite` — Every self-map on a finite nonempty type has a periodic point
* `image_chain_stabilizes` — The image chain f^[n](α) stabilizes in O(|α|) steps
* `closure_drift_bound_iterate_linear` — Iterate drift grows at most linearly
* `iterate_image_subset_of_invariant` — Invariant sets remain invariant under all iterates
* `exists_minimal_invariant_finset_by_descent` — Minimal invariant Finsets exist by descent
* `ultrafilter_cluster_point_of_proofSpectralCompact` — Ultrafilter cluster point extraction

Bridge: connects prime-spectrum compactness to post-quantum channel invariants.
Bridge: connects closure dynamics to thermodynamic entropy monotonicity.
-/


set_option maxHeartbeats 400000

universe u

open Set Function

/-! ## Section 1: Core Definitions — Closed Families and Compactness -/





/-! ## Section 2: Closure Dynamics and Admissibility -/







/-! ## Section 3: Stone–Čech Spectral Object -/


/-! ## Section 4: Iterate Invariance -/







/-! ## Section 5: Closure Operator Laws -/




/-! ## Section 6: Admissible Dynamics — Iterate Descent -/


/-! ## Section 7: Descending Chain Stabilization -/


/-! ## Section 8: Quantitative Bounds -/



/-! ## Section 9: FIP and Compactness -/




/-! ## Section 10: Extension Theorems -/



/-! ## Section 11: Galois Correspondence for Spectral Semantics -/


variable {S : Type*} [CommSemiring S]












/-! ## Section 12: Image Chain Stabilization -/




/-! ## Section 13: Periodic Orbit Existence -/




/-! ## Section 14: Minimal Invariant Sets -/


/-! ## Section 15: Channel Pair Symmetry -/


/-! ## Section 16: Closure Composition -/


/-! ## Section 17: Prime Separation -/



/-! ## Section 18: Certified Robustness -/



/-! ## Section 19: Idempotent Condensation -/


/-! ## Section 20: Existence of Invariant Set -/


/-! ## Section 21: Constructions -/



/-! ## Section 22: Application-Facing Summary Theorems -/






theorem solution    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) {K : Finset α} (hK : K.Nonempty) (hinv : ∀ x ∈ K, f x ∈ K) :
    ∃ x ∈ K, ∃ n : ℕ, n ≥ 1 ∧ f^[n] x = x := by
  obtain ⟨x₀, hx₀⟩ := hK
  have horbit : ∀ n, f^[n] x₀ ∈ K := by
    intro n; induction n with
    | zero => simpa
    | succ n ih => rw [iterate_succ_apply']; exact hinv _ ih
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (K.card + 1) => (⟨f^[(i : ℕ)] x₀, horbit i⟩ : K))
    (by simp [Fintype.card_fin, Fintype.card_coe])
  have heq' : f^[(i : ℕ)] x₀ = f^[(j : ℕ)] x₀ := congr_arg Subtype.val heq
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact ⟨f^[(i : ℕ)] x₀, horbit i, (j : ℕ) - (i : ℕ), by omega,
      by rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq'.symm⟩
  · exact ⟨f^[(j : ℕ)] x₀, horbit j, (i : ℕ) - (j : ℕ), by omega,
      by rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq'⟩
