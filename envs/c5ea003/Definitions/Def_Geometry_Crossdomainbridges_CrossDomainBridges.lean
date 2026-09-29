-- Prove2me | Definitions.Def_Geometry_Crossdomainbridges_CrossDomainBridges
-- name    : Geometry_Crossdomainbridges_CrossDomainBridges
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:03:46.534437+00:00
-- url     : https://prove2.me/theorems/92f0c624-37dc-4694-bfce-0c55f005fb96
-- title:
--   Aether Catalog definitions — Geometry_Crossdomainbridges_CrossDomainBridges
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Crossdomainbridges.CrossDomainBridges`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Crossdomainbridges/CrossDomainBridges.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Cross-Domain Information Bridges: ML, Physics, and Cryptography

## Overview

This file establishes deep cross-domain bridges connecting:
- **Machine Learning**: Neural network capacity bounds, gradient descent convergence
- **Physics**: Thermodynamic entropy, Boltzmann distributions, Hamiltonian bounds
- **Cryptography**: Lattice-based security, information-theoretic one-time pad security

## Bridge: connects MachineLearning to Physics to Cryptography
-/

open Finset Real BigOperators

noncomputable section

namespace CrossDomainBridges

/-! ## Section 1: Neural Network Information Capacity -/

/-- A neural network architecture specification.
    Bridge: connects MachineLearning (neural_network) to InformationTheory (capacity). -/
structure NeuralArchitecture where
  depth : ℕ
  width : ℕ
  bitsPerWeight : ℕ
  depth_pos : 0 < depth
  width_pos : 0 < width
  bits_pos : 0 < bitsPerWeight

/-- Total number of weight parameters: O(depth × width²). -/
def totalParams (arch : NeuralArchitecture) : ℕ :=
  arch.depth * arch.width * arch.width

/-- Information capacity in bits: params × bitsPerWeight. -/
def informationCapacity (arch : NeuralArchitecture) : ℕ :=
  totalParams arch * arch.bitsPerWeight




/-! ## Section 2: Thermodynamic-Information Bridge -/

/-- A thermodynamic system state with energy and entropy.
    Bridge: connects Physics (thermodynamics) to InformationTheory (entropy). -/
structure ThermoState where
  energy : ℝ
  entropy : ℝ
  temperature : ℝ
  entropy_nonneg : 0 ≤ entropy
  temp_pos : 0 < temperature

/-- Free energy: F = E - T·S. -/
def freeEnergy (s : ThermoState) : ℝ :=
  s.energy - s.temperature * s.entropy




/-! ## Section 3: Cryptographic Security from Entropy -/

/-- A one-time pad encryption scheme.
    Bridge: connects Cryptography (one-time pad) to InformationTheory (perfect secrecy). -/
structure OneTimePad where
  messageLen : ℕ
  keyLen : ℕ
  perfect_secrecy : messageLen ≤ keyLen




/-! ## Section 4: Gradient Descent Convergence via Entropy -/

/-- A convex optimization problem specification. -/
structure ConvexOptProblem where
  gradLipschitz : ℝ
  strongConvexity : ℝ
  initialGap : ℝ
  lip_pos : 0 < gradLipschitz
  sc_nonneg : 0 ≤ strongConvexity
  gap_pos : 0 < initialGap

/-- Gradient descent convergence rate: O(L·D²/T). -/
def convexConvergenceRate (prob : ConvexOptProblem) (T : ℕ) : ℝ :=
  if T = 0 then prob.initialGap
  else prob.gradLipschitz * prob.initialGap / T



/-! ## Section 5: LWE Information Bounds -/

/-- An LWE (Learning With Errors) instance. -/
structure LWEInstance where
  n : ℕ
  m : ℕ
  q : ℕ
  n_pos : 0 < n
  m_ge_n : n ≤ m
  q_ge : 2 ≤ q

/-- Total information in LWE samples: m · log₂(q) bits. -/
def lweSampleEntropy (inst : LWEInstance) : ℕ := inst.m * Nat.log 2 inst.q

/-- Secret information: n · log₂(q) bits. -/
def lweSecretInfo (inst : LWEInstance) : ℕ := inst.n * Nat.log 2 inst.q



/-! ## Section 6: Boltzmann Distribution -/

/-- A discrete energy landscape.
    Bridge: connects Physics (statistical mechanics) to MachineLearning (softmax). -/
structure EnergyLandscape (n : ℕ) where
  energies : Fin n → ℝ
  invTemp : ℝ
  invTemp_pos : 0 < invTemp

/-- Boltzmann weight of state i: exp(-β · E_i). -/
def boltzmannWeight {n : ℕ} (landscape : EnergyLandscape n) (i : Fin n) : ℝ :=
  Real.exp (-landscape.invTemp * landscape.energies i)



/-! ## Section 7: Entropy Production and Irreversibility -/

/-- An irreversible process.
    Bridge: connects Physics (irreversibility) to Cryptography (one-way functions). -/
structure IrreversibleProcess where
  inputEntropy : ℝ
  outputEntropy : ℝ
  entropyProduction : ℝ
  input_nonneg : 0 ≤ inputEntropy
  output_nonneg : 0 ≤ outputEntropy
  production_nonneg : 0 ≤ entropyProduction
  second_law : inputEntropy + entropyProduction ≤ outputEntropy




/-! ## Section 8: PAC Learning Bounds -/

/-- A PAC learning problem.
    Bridge: connects MachineLearning (PAC learning) to InformationTheory. -/
structure PACLearningProblem where
  vcDimension : ℕ
  errorTolerance : ℝ
  confidence : ℝ
  vc_pos : 0 < vcDimension
  err_pos : 0 < errorTolerance
  err_lt_one : errorTolerance < 1
  conf_pos : 0 < confidence

/-- Sample complexity lower bound: Ω(d/ε). -/
def sampleComplexityBound (prob : PACLearningProblem) : ℝ :=
  prob.vcDimension / prob.errorTolerance




/-! ## Section 9: The Entropy Triangle -/

/-- The entropy triangle: three entropy bounds from different domains.
    Bridge: connects InformationTheory to Physics to Cryptography. -/
structure EntropyTriangle where
  shannonEntropy : ℝ
  thermoEntropy : ℝ
  cryptoEntropy : ℝ
  shannon_nonneg : 0 ≤ shannonEntropy
  thermo_nonneg : 0 ≤ thermoEntropy
  crypto_nonneg : 0 ≤ cryptoEntropy
  crypto_le_shannon : cryptoEntropy ≤ shannonEntropy
  shannon_le_thermo : shannonEntropy ≤ thermoEntropy





end CrossDomainBridges


