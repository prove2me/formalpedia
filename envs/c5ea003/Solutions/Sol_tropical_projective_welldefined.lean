-- Prove2me | solution 1 for tropical_projective_welldefined
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:27:48.878011+00:00
-- url     : https://prove2.me/submissions/95f10326-bb8d-44d2-8a23-b2041cededd5

-- Sol generated from Bridges/TropicalCryptoMLBridge.lean
import Mathlib
import Definitions.Def_Bridges_TropicalCryptoMLBridge
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical-Crypto-ML Bridge: Collision Resistance, Preimage Hardness, and
  Thermodynamic Entropy Bounds

## Bridge: Tropical Geometry × Lattice Cryptography × Statistical Mechanics

The unifying insight: the tropical (min-plus) semiring structure ensures that
the minimum of translated functions is non-expansive. This single algebraic
property simultaneously gives:
- Collision resistance (distinct inputs produce separated outputs)
- Certified robustness (small perturbations cause small output changes)
- Entropy monotonicity (tropical maps preserve entropy structure)

## Main Definitions

* `TropProjectiveEquiv` — equivalence class modulo constant shifts
* `IsTropProjectivelyInjective` — projective injectivity for collision resistance
* `minPlusConv` — min-plus convolution for tropical transforms
* `tropicalEntropy` — discrete tropical entropy
* `TropicalKeyExchange` — tropical Diffie-Hellman key exchange
* `IsTropicallyConvex` — tropical convexity for robustness regions

## Main Results

* `tropical_projective_welldefined` — tropical maps descend to projective space
* `tropical_collision_resistance` — injectivity implies collision resistance
* `tropicalEntropy_le_dim` — entropy bounded by dimension
* `tropicalEntropy_shift_invariant` — entropy is a projective invariant
* `tropical_key_exchange_robustness` — key exchange noise tolerance
* `tropical_triple_bridge` — master bridge: crypto + ML + entropy
-/

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## Section 1: Core Operations -/



/-! ## Section 2: Tropical Projective Space -/






/-! ## Section 3: Collision Resistance -/



/-! ## Section 4: Min-Plus Convolution -/



/-! ## Section 5: Tropical Entropy Theory -/






/-! ## Section 6: Tropical Key Exchange -/





/-! ## Section 7: Preimage Theory -/



/-! ## Section 8: Berggren Connection -/


/-! ## Section 9: Tropical Convexity -/



/-! ## Section 10: Master Bridge Theorem -/



theorem solution{n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℤ)
    {x y : Fin n → ℤ} (h : TropProjectiveEquiv x y) :
    TropProjectiveEquiv (tropMVB A x) (tropMVB A y) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i => ?_⟩
  simp only [tropMVB]
  have heq : (fun j => A i j + x j) = (fun j => (A i j + y j) + c) := by
    ext j; rw [hc j]; ring
  rw [heq]
  apply le_antisymm
  · obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun j => A i j + y j)
    calc Finset.inf' Finset.univ Finset.univ_nonempty (fun j => (A i j + y j) + c)
        ≤ (A i j₀ + y j₀) + c := Finset.inf'_le _ (Finset.mem_univ j₀)
      _ = Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A i j + y j) + c := by
          rw [hj₀]
  · apply Finset.le_inf' Finset.univ_nonempty
    intro j _
    exact Int.add_le_add_right
      (Finset.inf'_le (fun j => A i j + y j) (Finset.mem_univ j)) c
