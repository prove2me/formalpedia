-- Prove2me | solution 1 for QuantumTropical.tropWeightEnumerator_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:07.613583+00:00
-- url     : https://prove2.me/submissions/184d70c3-2499-4c30-bc37-732980d62bac

-- Sol generated from Bridges/QuantumTropicalCore.lean
import Mathlib
import Definitions.Def_Bridges_QuantumTropicalCore
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


open QuantumTropical

open Finset Finsupp

/-! ## Section 1: Core Definitions -/







variable {ι : Type*} [DecidableEq ι]







/-! ## Section 2: Pauli Weight Properties -/



/-! ## Section 3: Basic Valuation Algebra -/








/-! ## Section 4: Tropical Enumerator Properties -/




/-- A witness at weight k gives a finite upper bound on the enumerator.
Bridge: a certified quantum codeword at weight k bounds the tropical profile. -/
theorem tropWeightEnumerator_le_of_mem (v : StabilizerValuation ι)
    {S : Finset (ι →₀ ℕ)} {f : ι →₀ ℕ} (hf : f ∈ S)
    {k : ℕ} (hw : pauliWeight f = k) :
    tropWeightEnumerator v S k ≤ v.val f := by
  unfold tropWeightEnumerator
  exact le_trans (Finset.inf_le hf) (by simp [hw])




/-! ## Section 5: Closure Operator and Fixed-Point Theory -/








/-! ## Section 6: Tropical Breakpoint and Distance Lower Bound -/






/-! ## Section 7: Inf-Convolution Properties -/








/-! ## Section 8: Tropical Support Function -/





/-! ## Section 9: Concatenation and Recovery -/






/-! ## Section 10: Thermodynamic and Collision Bounds -/







open QuantumTropical in
theorem solution(v : StabilizerValuation ι)
    (S : Finset (ι →₀ ℕ)) (k : ℕ) :
    tropWeightEnumerator v S k = ⊤ ↔
      ∀ f ∈ S, pauliWeight f = k → v.val f = ⊤ := by
  constructor
  · intro htop f hf hw
    have hle := tropWeightEnumerator_le_of_mem v hf hw
    rw [htop] at hle
    exact WithTop.top_le_iff.mp hle
  · intro h
    simp only [tropWeightEnumerator]
    rw [Finset.inf_eq_top_iff]
    intro f hf
    by_cases hw : pauliWeight f = k
    · simp [hw, h f hf hw]
    · simp [hw]
