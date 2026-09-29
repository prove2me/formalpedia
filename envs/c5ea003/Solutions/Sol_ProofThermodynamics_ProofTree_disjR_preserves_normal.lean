-- Prove2me | solution 1 for ProofThermodynamics.ProofTree.disjR_preserves_normal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:29:45.407993+00:00
-- url     : https://prove2.me/submissions/eed06dbf-e489-4174-bf91-8032ea7f0b0f

-- Sol generated from Bridges/ProofThermodynamicsCore.lean
import Mathlib
import Definitions.Def_Bridges_ProofThermodynamicsCore
/-
  Proof Thermodynamics Core: Formula Energy, Proof Trees, and Conservation Laws

  Bridge: Proof Theory ↔ Statistical Mechanics ↔ Information Theory

  This file establishes the foundational definitions and structural theorems for
  proof thermodynamics: a rigorous correspondence between sequent calculus proof
  normalization and thermodynamic processes.
-/

open ProofThermodynamics


open Formula




















/-! ## Proof Trees -/


open ProofTree







/-! ### First Law: Energy Conservation -/






/-! ### Structural Properties -/



























/-! ## Boltzmann Weights and Partition Functions -/











open ProofThermodynamics.ProofTree in
theorem solution{π₁ π₂ : ProofTree}
    (h1 : is_normal π₁) (h2 : is_normal π₂) :
    is_normal (disjR π₁ π₂) := by
  simp [is_normal, cut_count] at *; omega
