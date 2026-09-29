-- Prove2me | Definitions.Def_Bridges_TropicalCryptoMLBridge
-- name    : Bridges_TropicalCryptoMLBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:58.561074+00:00
-- url     : https://prove2.me/theorems/9e9708e4-e1e7-4881-97f5-605e610f4e99
-- title:
--   Aether Catalog definitions — Bridges_TropicalCryptoMLBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalCryptoMLBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalCryptoMLBridge.lean by skeleton subtraction
import Mathlib
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

/-- Tropical min-plus matrix-vector product.
    Bridge: core primitive for both lattice_crypto and neural_network. -/
def tropMVB {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    Fin n → ℤ :=
  fun i => Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A i j + x j)

/-- L∞ distance. -/
def linfDistB {n : ℕ} (x y : Fin n → ℤ) : ℕ :=
  Finset.sup Finset.univ (fun i => (x i - y i).natAbs)

/-! ## Section 2: Tropical Projective Space -/

/-- Two vectors are **tropically projectively equivalent** if they differ
    by a constant shift. This defines tropical projective space TP^{n-1}.
    Bridge: the natural domain for post_quantum tropical one-way functions. -/
def TropProjectiveEquiv {n : ℕ} (x y : Fin n → ℤ) : Prop :=
  ∃ c : ℤ, ∀ i : Fin n, x i = y i + c





/-! ## Section 3: Collision Resistance -/

/-- A tropical map is **projectively injective** if it maps distinct
    projective classes to distinct projective classes.
    Bridge: ensures post_quantum collision resistance. -/
def IsTropProjectivelyInjective {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ x y : Fin n → ℤ,
    TropProjectiveEquiv (tropMVB A x) (tropMVB A y) →
    TropProjectiveEquiv x y


/-! ## Section 4: Min-Plus Convolution -/

/-- **Min-plus convolution** of two integer sequences (cyclic).
    `(f ⊛ g)(k) = min_i (f(i) + g((k-i) mod n))`
    Bridge: tropical polynomial multiplication for NTRU-like crypto. -/
def minPlusConv {n : ℕ} [NeZero n] (f g : Fin n → ℤ) : Fin n → ℤ :=
  fun k => Finset.inf' Finset.univ Finset.univ_nonempty
    (fun i => f i + g ⟨(k.val - i.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩)


/-! ## Section 5: Tropical Entropy Theory -/

/-- **Tropical entropy**: number of distinct values in an integer vector.
    Bridge: connects tropical algebra to information-theoretic security
    and thermodynamic entropy bounds. -/
def tropicalEntropy {n : ℕ} (x : Fin n → ℤ) : ℕ :=
  (Finset.univ.image x).card





/-! ## Section 6: Tropical Key Exchange -/





/-! ## Section 7: Preimage Theory -/



/-! ## Section 8: Berggren Connection -/


/-! ## Section 9: Tropical Convexity -/

/-- A set is **tropically convex** if it is closed under tropical
    convex combinations.
    Bridge: tropical convexity governs both certified_robustness regions
    and lattice_crypto module structure. -/
def IsTropicallyConvex {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∀ x y : Fin n → ℤ, x ∈ S → y ∈ S →
    ∀ t : ℤ, (fun i => min (x i + t) (y i)) ∈ S


/-! ## Section 10: Master Bridge Theorem -/


end


