-- Prove2me | solution 1 for tropical_key_exchange_robustness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:27:21.811073+00:00
-- url     : https://prove2.me/submissions/e462ddc0-4d94-4f53-8116-17e6c183a148

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
    (pub pub' : Fin n → ℤ) :
    linfDistB (tropMVB A pub) (tropMVB A pub') ≤ linfDistB pub pub' := by
  apply Finset.sup_le; intro i _
  -- Two one-sided bounds
  suffices h : ∀ u v : Fin n → ℤ,
      tropMVB A u i - tropMVB A v i ≤ ↑(linfDistB u v) by
    have h1 := h pub pub'
    have h2 := h pub' pub
    have hcomm : linfDistB pub' pub = linfDistB pub pub' := by
      simp only [linfDistB]; congr 1; ext j; rw [← Int.natAbs_neg, neg_sub]
    rw [hcomm] at h2; omega
  intro u v
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j => A i j + v j)
  calc tropMVB A u i - tropMVB A v i
      = Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A i j + u j) -
        Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A i j + v j) := rfl
    _ ≤ (A i j₀ + u j₀) - (A i j₀ + v j₀) := by
        apply sub_le_sub
        · exact Finset.inf'_le _ (Finset.mem_univ _)
        · exact hj₀.ge
    _ = u j₀ - v j₀ := by ring
    _ ≤ |u j₀ - v j₀| := le_abs_self _
    _ = ↑(u j₀ - v j₀).natAbs := Int.abs_eq_natAbs _
    _ ≤ ↑(linfDistB u v) := by
        exact_mod_cast Finset.le_sup (f := fun i => (u i - v i).natAbs) (Finset.mem_univ j₀)
