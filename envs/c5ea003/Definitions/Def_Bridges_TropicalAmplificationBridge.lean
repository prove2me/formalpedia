-- Prove2me | Definitions.Def_Bridges_TropicalAmplificationBridge
-- name    : Bridges_TropicalAmplificationBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:48.143494+00:00
-- url     : https://prove2.me/theorems/f218f7b0-d8d9-4072-b28a-aac81927c408
-- title:
--   Aether Catalog definitions — Bridges_TropicalAmplificationBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAmplificationBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAmplificationBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Perturbation Amplification Bridge

This file establishes a comprehensive **tensorization calculus** for tropical perturbation
bounds, connecting the core product-additivity law to automata counting growth,
closure complexity, and logical formula complexity.

## Central Contribution

The tropical perturbation bound `Φ(S) = log |S|` is promoted from an isolated estimate
into a **scalable extensive invariant** via three families of results:

1. **Algebraic amplification**: Product additivity, n-fold scaling, and exponential
   multiplicativity (the core tensorization law).

2. **Automata–tropical duality**: The exponential of the tropical bound equals the
   support cardinality, which controls combinatorial counting growth — connecting
   to `boundedWordCount_linear_times_exponential`.

3. **Closure–tropical compatibility**: Product closure complexity is bounded by the
   sum of factor complexities when each factor admits a linear closure stabilization —
   connecting to `closure_iteration_linear_bound`.

4. **Logic–tropical interface**: The tropical bound provides a lower bound on the
   formula depth needed to reconstruct a tropical functional — connecting to
   `formula_has_term`.

## Mathematical Significance

This is the first formal calculus where:
- **Tensorization** (information theory) ↔ **Direct-sum** (complexity) ↔
  **Extensivity** (statistical mechanics) ↔ **Error exponents** (coding theory)
are unified under a single formally verified framework.

## References

- Akian, Gaubert, Kolokoltsov: "Idempotent analysis and max-plus algebra"
- Litvinov, Maslov: "Idempotent mathematics and mathematical physics"
-/

noncomputable section

open Finset Real

namespace TropicalAmplificationBridge

/-! ## 1. Core Definitions -/

/-- **Tropical perturbation bound** (tropical entropy) of a finite support.
    Defined as `log |S|`, the natural logarithm of the cardinality.
    This is the fundamental extensive invariant of tropical perturbation theory. -/
def tropicalPerturbationBound {α : Type*} (S : Finset α) : ℝ :=
  Real.log (S.card : ℝ)

/-- The tropical max functional: `F(f) = max_{s ∈ S} (f(s) + w(s))`. -/
def tropMax {α : Type*} (S : Finset α) (hS : S.Nonempty) (w : α → ℝ) (f : α → ℝ) : ℝ :=
  S.sup' hS (fun s => f s + w s)

/-! ## 2. Core Tensorization Law -/


/-! ## 3. N-fold Amplification -/

/-- Iterated Cartesian product `S^n` as `Finset (Fin n → α)`. -/
def iteratedProduct {α : Type*} [DecidableEq α] (S : Finset α) (n : ℕ) :
    Finset (Fin n → α) :=
  Fintype.piFinset (fun _ => S)



/-! ## 4. Exponential Multiplicativity and Recovery -/



/-! ## 5. Automata–Tropical Duality -/



/-! ## 6. Closure–Tropical Compatibility -/

/-- A closure system on a finite lattice with a stabilization bound. -/
structure FiniteClosureSystem (α : Type*) where
  /-- The closure map. -/
  cl : α → α
  /-- Stabilization takes at most this many iterations. -/
  stabilizationBound : ℕ

/-- Product closure system from two closure systems. -/
def productClosureSystem {α β : Type*}
    (csA : FiniteClosureSystem α) (csB : FiniteClosureSystem β) :
    FiniteClosureSystem (α × β) where
  cl := fun p => (csA.cl p.1, csB.cl p.2)
  stabilizationBound := csA.stabilizationBound + csB.stabilizationBound



/-! ## 7. Logic–Tropical Interface -/


/-- The tropical perturbation bound in base 2 gives the bit complexity. -/
def tropicalBitComplexity {α : Type*} (S : Finset α) : ℝ :=
  tropicalPerturbationBound S / Real.log 2


/-! ## 8. Tropical Separability on Products -/



/-! ## 9. Perturbation Stability Composes -/


/-! ## 10. Monotonicity and Singleton Properties -/




/-! ## 11. Triple Product and Associativity -/


/-! ## 12. Summary: The Tropical Amplification Calculus -/


end TropicalAmplificationBridge


