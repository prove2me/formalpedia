-- Prove2me | solution 1 for TropicalGaloisSolvability.owf_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:27.952672+00:00
-- url     : https://prove2.me/submissions/ed9d6a79-7f88-44ea-a582-cc96af8f9ca3

-- Sol generated from Bridges/TropicalGaloisSolvability.lean
import Mathlib
import Definitions.Def_Bridges_TropicalGaloisSolvability
import Theorems.Thm_TropicalGaloisSolvability_brute_force_complexity
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Galois Solvability and the Abel-Ruffini Correspondence

## Overview

This file develops the connection between **tropical polynomial solvability** and
**group-theoretic solvability**, culminating in concrete versions of the tropical
Abel-Ruffini theorem.

**Bridge: connects tropical algebra ↔ group theory ↔ certified ML robustness ↔ cryptography**

## Main Results

* `s5_not_solvable` — S₅ is not solvable (Abel-Ruffini core)
* `s5_commutator_nontrivial` — [S₅, S₅] ≠ ⊥ (solvability obstruction)
* `tropical_galois_embedding_bound` — |Gal| divides n!
* `robustness_complexity_tradeoff` — Simpler models ⟹ more robust
* `tropical_hash_preimage_growth` — n preimage collisions for any n
* `tower_degree_exponential` — Radical tower degree ≥ 2^height
* `index_degree_relationship` — Lagrange's theorem for Galois groups
-/

open Finset Function

open TropicalGaloisSolvability

/-! ## Section 1: Tropical Monomial Algebra -/







/-! ## Section 2: The Solvability Hierarchy -/








/-! ## Section 3: Galois Group Size Bounds -/





/-! ## Section 4: Certified Robustness -/





/-! ## Section 5: Tropical Hash Function Theory -/




/-! ## Section 6: Radical Tower Theory -/





/-! ## Section 7: Brute-Force Complexity -/



/-! ## Section 8: Galois Correspondence — Structural Lemmas -/





/-! ## Section 9: Concrete Computations -/







open TropicalGaloisSolvability in
theorem solution(n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ Nat.factorial n := by
  have hsq : n ^ 2 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m ≤ 4
      · interval_cases m <;> omega
      · push_neg at hm
        have ihm := ih (by omega)
        have hm3 : 2 * m + 1 ≤ m ^ 2 := by nlinarith
        have : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
        nlinarith
  linarith [brute_force_complexity n hn]
