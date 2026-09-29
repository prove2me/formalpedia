-- Prove2me | Definitions.Def_Bridges_QuantumTropicalCore
-- name    : Bridges_QuantumTropicalCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:11.118566+00:00
-- url     : https://prove2.me/theorems/df44e939-b277-40eb-8e82-625891fb6bf1
-- title:
--   Aether Catalog definitions — Bridges_QuantumTropicalCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantumTropicalCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantumTropicalCore.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Valuation–Stabilizer Correspondence and Tropical Quantum Code Geometry

This file formalizes a min-plus/tropical theory of quantum stabilizer weight data.
It turns closure-theoretic stabilizer certification into explicit lower bounds on
code distance and explicit inf-convolution formulas for concatenated recovery.

Bridge: connects quantum error correction, tropical/idempotent algebra,
lattice fixed-point theory, polyhedral support functions, and certified
robustness style min-plus verification.

## Main definitions

* `QuantumTropical.StabilizerValuation` — tropical valuation on Pauli-weight vectors
* `QuantumTropical.tropWeightEnumerator` — min-plus weight enumerator
* `QuantumTropical.IsClosureOperator` — closure operator structure
* `QuantumTropical.IsTropicalBreakpoint` — breakpoint for distance certification
* `QuantumTropical.infConvolutionNat` — min-plus inf-convolution
* `QuantumTropical.tropicalSupportFunction` — tropical support function
* `QuantumTropical.TropicalClosureCompatible` — closure-valuation compatibility

## Main results

* `quantum_certified_breakpoint_distance` — breakpoint implies distance lower bound
* `breakpoint_add_of_both` — concatenation breakpoint ≥ sum of breakpoints
* `tropicalSupportFunction_infimal` — support function distributes over union
* `lattice_fixedpoint_pauli_shadow` — fixed-point invariance of enumerators
-/


namespace QuantumTropical

open Finset Finsupp

/-! ## Section 1: Core Definitions -/

/-- Pauli weight of a finitely supported function: total sum of multiplicities.
Bridge: connects quantum Pauli operators to tropical weight lattice.
Computing `pauliWeight f` is O(|support f|). -/
noncomputable def pauliWeight {ι : Type*} [DecidableEq ι] (f : ι →₀ ℕ) : ℕ :=
  f.sum (fun _ m => m)

/-- Tropical valuation data attached to finitely supported Pauli-weight observables.
Bridge: connects quantum stabilizer enumerators to tropical lattice valuations.
Quantum interpretation: `val f` measures the tropical cost of realizing the
Pauli operator with weight profile `f` in a stabilizer code.
The `finite_val` condition ensures all elements have finite (non-⊤) valuations,
which is necessary for certified distance lower bounds. -/
structure StabilizerValuation (ι : Type*) [DecidableEq ι] where
  /-- The valuation function mapping weight vectors to tropical values -/
  val : (ι →₀ ℕ) → WithTop ℕ
  /-- Monotonicity: larger weight vectors have larger valuations -/
  monotone_val : Monotone val
  /-- The zero vector maps to zero (identity element) -/
  val_zero : val 0 = 0
  /-- Subadditivity: quantum concatenation cost is at most the sum -/
  val_add_le : ∀ f g, val (f + g) ≤ val f + val g
  /-- All valuations are finite: necessary for certified distance bounds -/
  finite_val : ∀ f, val f ≠ ⊤

/-- Closure operator structure for lattice fixed-point theory.
Bridge: connects Knaster-Tarski fixed-point lattice theory to
quantum stabilizer certification. -/
structure IsClosureOperator {α : Type*} [Preorder α] (c : α → α) : Prop where
  /-- The closure is extensive: every element is below its closure -/
  extensive : ∀ x, x ≤ c x
  /-- The closure is monotone -/
  monotone' : Monotone c
  /-- The closure is idempotent -/
  idempotent' : ∀ x, c (c x) = c x

/-- Fixed points of a function, representing certified codespace elements.
Bridge: connects lattice fixed-point theory to quantum code certification. -/
def fixedPoints {α : Type*} (c : α → α) : Set α := {x | c x = x}

/-- Tropical breakpoint: all weights below d have infinite tropical cost.
Bridge: connects tropical geometry breakpoints to quantum code distance
certification and post_quantum_security hardness gaps. -/
def IsTropicalBreakpoint (W : ℕ → WithTop ℕ) (d : ℕ) : Prop :=
  ∀ k, k < d → W k = ⊤

/-- Compatibility between closure operators and tropical valuations.
Bridge: connects lattice closure semantics to certified tropical shadow
computation for quantum stabilizer codespaces. -/
class TropicalClosureCompatible
    {α : Type*} [Preorder α] (c : α → α) (φ : α → WithTop ℕ) : Prop where
  /-- Monotonicity through closure -/
  mono_closed : ∀ ⦃x y : α⦄, x ≤ y → φ (c x) ≤ φ (c y)
  /-- Idempotent shadow: double closure doesn't change the valuation -/
  idempotent_shadow : ∀ x, φ (c (c x)) = φ (c x)

variable {ι : Type*} [DecidableEq ι]

/-- Tropical weight enumerator: for each weight k, the minimum tropical cost
among all elements of S with Pauli weight k.
Bridge: connects quantum weight enumerators to tropical min-plus profiles.
Computing `tropWeightEnumerator v S k` is O(|S|) by scanning S. -/
noncomputable def tropWeightEnumerator (v : StabilizerValuation ι)
    (S : Finset (ι →₀ ℕ)) (k : ℕ) : WithTop ℕ :=
  S.inf (fun f => if pauliWeight f = k then v.val f else ⊤)

/-- Min-plus inf-convolution on WithTop ℕ: the tropical analogue of convolution.
Bridge: connects tropical algebra to quantum concatenated recovery channels.
Computing `infConvolutionNat f g n` is O(n) by scanning 0..n.
Computing the first N values is O(N²) naively. -/
def infConvolutionNat (f g : ℕ → WithTop ℕ) (n : ℕ) : WithTop ℕ :=
  (Finset.range (n + 1)).inf (fun i => f i + g (n - i))

/-- Tropical support function over a finite set of weight vectors.
Bridge: connects polyhedral/tropical geometry support functions
to quantum stabilizer code analysis. -/
noncomputable def tropicalSupportFunction
    (S : Finset (ι →₀ ℕ)) (x : ι →₀ ℕ) : WithTop ℕ :=
  S.inf (fun f => ↑(pauliWeight (f + x)))

/-- Support radius of a stabilizer valuation: the supremum of valuations.
Bridge: connects tropical valuation radius to quantum code parameters. -/
noncomputable def supportRadius (v : StabilizerValuation ι)
    (S : Finset (ι →₀ ℕ)) : WithTop ℕ :=
  S.sup (fun f => v.val f)


/-- The valuation polytope: set of weight vectors with bounded valuation.
Bridge: connects tropical code polytopes to certified quantum code
distance and post_quantum_security analysis. -/
noncomputable def valuationPolytope (v : StabilizerValuation ι)
    (S : Finset (ι →₀ ℕ)) (bound : WithTop ℕ) : Finset (ι →₀ ℕ) :=
  S.filter (fun f => v.val f ≤ bound)

/-! ## Section 2: Pauli Weight Properties -/



/-! ## Section 3: Basic Valuation Algebra -/








/-! ## Section 4: Tropical Enumerator Properties -/








/-! ## Section 5: Closure Operator and Fixed-Point Theory -/








/-! ## Section 6: Tropical Breakpoint and Distance Lower Bound -/






/-! ## Section 7: Inf-Convolution Properties -/








/-! ## Section 8: Tropical Support Function -/





/-! ## Section 9: Concatenation and Recovery -/

/-- Concatenated recovery enumerator defined as inf-convolution of
individual tropical weight enumerators.
Bridge: certified_concat_recovery_infimal — quantum concatenated
recovery channels compose via min-plus convolution. -/
noncomputable def concatRecoveryEnumerator
    (v₁ : StabilizerValuation ι) (v₂ : StabilizerValuation ι)
    (S₁ S₂ : Finset (ι →₀ ℕ)) : ℕ → WithTop ℕ :=
  infConvolutionNat (tropWeightEnumerator v₁ S₁) (tropWeightEnumerator v₂ S₂)





/-! ## Section 10: Thermodynamic and Collision Bounds -/






end QuantumTropical


