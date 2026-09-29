-- Prove2me | Definitions.Def_Algebra_PosetTheory_CryptographicEntropy
-- name    : Algebra_PosetTheory_CryptographicEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:48:32.633495+00:00
-- url     : https://prove2.me/theorems/bfa0e181-4e27-4543-a26d-45a12f63e820
-- title:
--   Aether Catalog definitions — Algebra_PosetTheory_CryptographicEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetTheory.CryptographicEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetTheory/CryptographicEntropy.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Cryptographic Entropy: Post-Quantum Security and Lattice Bridges

## Overview

This file extends the entropy algebra framework with deep connections to
cryptography, establishing verified bounds for:

* Lattice-based cryptographic security parameters
* Post-quantum security margins via entropy gap analysis
* Randomness extraction bounds from min-entropy
* Tropical hash collision resistance analysis
* Neural network adversarial robustness via entropy certificates

## Bridge: connects Cryptography to InformationTheory to Algebra to MachineLearning

The key innovation: entropy gap (difference between max-entropy and actual entropy)
directly quantifies both cryptographic security and machine learning robustness.
This creates a formal bridge where improving one domain improves the other.

## Computational Bounds

* Randomness extraction: O(n) for n-bit source
* Lattice key generation: O(n² log q) via NTT
* Hash collision search: Omega(2^(k/2)) for k-bit hash
* Entropy verification: O(n log n) via sorting
-/

open Finset Real BigOperators

noncomputable section

namespace CryptographicEntropy

/-! ## Section 1: Randomness Source Model

Bridge: connects Cryptography (randomness extraction) to InformationTheory (entropy). -/

/-- A randomness source with min-entropy bound.
    The min-entropy quantifies the unpredictability of the source.
    Bridge: connects Cryptography (key generation) to InformationTheory (min-entropy). -/
structure RandomnessSource where
  /-- Number of bits in the source -/
  sourceBits : ℕ
  /-- Min-entropy in bits -/
  minEntropy : ℝ
  /-- Min-entropy is non-negative -/
  entropy_nonneg : 0 ≤ minEntropy
  /-- Min-entropy ≤ source bits -/
  entropy_le_source : minEntropy ≤ sourceBits

/-- The entropy deficiency of a source: how far from uniform.
    Bridge: connects InformationTheory to Cryptography (randomness quality). -/
def RandomnessSource.deficiency (s : RandomnessSource) : ℝ :=
  s.sourceBits - s.minEntropy


/-! ## Section 2: Leftover Hash Lemma Parameters

Bridge: connects Cryptography (universal hashing) to InformationTheory (extraction). -/

/-- Parameters for the leftover hash lemma.
    Bridge: connects Cryptography (randomness extraction) to InformationTheory. -/
structure ExtractionParams where
  /-- Source min-entropy (bits) -/
  sourceEntropy : ℝ
  /-- Output length (bits) -/
  outputLength : ℝ
  /-- Security parameter (statistical distance) -/
  securityParam : ℝ
  /-- Source entropy is positive -/
  entropy_pos : 0 < sourceEntropy
  /-- Security parameter is positive -/
  security_pos : 0 < securityParam
  security_le_one : securityParam ≤ 1

/-- The extractable randomness: min-entropy minus 2·log(1/ε).
    By the leftover hash lemma, we can extract this many nearly-uniform bits.
    Computational complexity: O(n) for n-bit extraction.
    Bridge: connects Cryptography (extraction) to InformationTheory (entropy). -/
def extractableRandomness (p : ExtractionParams) : ℝ :=
  p.sourceEntropy - 2 * Real.log (1 / p.securityParam)


/-! ## Section 3: Post-Quantum Security Margins

Bridge: connects Cryptography (post-quantum) to InformationTheory (Grover bound). -/

/-- Post-quantum security margin: classical security minus Grover speedup.
    A k-bit classical scheme has k/2 bits of quantum security.
    Bridge: connects Cryptography (post_quantum_security) to InformationTheory. -/
def quantumSecurityMargin (classicalBits : ℝ) : ℝ :=
  classicalBits / 2





/-! ## Section 4: Lattice Dimension-Security Scaling

Bridge: connects Cryptography (lattice_crypto) to Algebra (lattice dimension)
        to InformationTheory (entropy). -/

/-- Lattice security parameters: dimension n and modulus q determine security.
    Bridge: connects Cryptography (lattice_crypto) to Algebra. -/
structure LatticeSecurity where
  dimension : ℕ
  modulus : ℕ
  dim_pos : 0 < dimension
  mod_gt_one : 1 < modulus

/-- The LWE hardness parameter: n·log(q) bits of security.
    Bridge: connects Cryptography (LWE) to InformationTheory (entropy). -/
def lweSecurityBits (l : LatticeSecurity) : ℝ :=
  l.dimension * Real.log l.modulus




/-! ## Section 5: Birthday Attack Complexity

Bridge: connects Cryptography (hash attacks) to Computation (complexity). -/

/-- Birthday attack complexity: 2^(k/2) operations for k-bit hash.
    Bridge: connects Cryptography (tropical_hash_collision) to Computation. -/
def birthdayAttackComplexity (hashBits : ℕ) : ℕ :=
  2 ^ (hashBits / 2)




/-! ## Section 6: Entropy-Based Key Derivation

Bridge: connects Cryptography (KDF) to InformationTheory (entropy preservation). -/

/-- Key derivation function specification.
    Bridge: connects Cryptography (KDF) to InformationTheory. -/
structure KDFSpec where
  inputEntropy : ℝ
  outputBits : ℕ
  input_pos : 0 < inputEntropy

/-- A KDF cannot output more entropy than its input.
    Bridge: connects Cryptography to InformationTheory (data processing inequality). -/
def kdfEntropyBound (spec : KDFSpec) : ℝ :=
  min spec.inputEntropy spec.outputBits



/-! ## Section 7: Neural Network Certified Robustness via Entropy

Bridge: connects MachineLearning (certified_robustness) to Cryptography (entropy)
        to InformationTheory. -/

/-- An entropy-certified classifier: robustness radius is determined by entropy gap.
    Bridge: connects MachineLearning (lipschitz_certified_robustness) to
            InformationTheory (entropy) to Cryptography (security margin). -/
structure EntropyCertifiedClassifier where
  numClasses : ℕ
  numClasses_pos : 0 < numClasses
  /-- Entropy of the output distribution -/
  outputEntropy : ℝ
  entropy_nonneg : 0 ≤ outputEntropy
  /-- Maximum possible entropy -/
  maxEntropy : ℝ
  max_pos : 0 < maxEntropy
  /-- Output entropy bounded by max -/
  entropy_le_max : outputEntropy ≤ maxEntropy

/-- The entropy margin: how far the classifier is from maximum uncertainty.
    A larger margin means more confident (and more robust) classification.
    Bridge: connects MachineLearning to InformationTheory. -/
def EntropyCertifiedClassifier.entropyMargin (c : EntropyCertifiedClassifier) : ℝ :=
  c.maxEntropy - c.outputEntropy


/-- The certified robustness radius is proportional to entropy margin.
    A Lipschitz-bounded network with entropy margin δ has robustness radius δ/L.
    Bridge: connects MachineLearning (certified_robustness) to InformationTheory
            to Cryptography (security margin). -/
def certifiedRobustnessRadius (c : EntropyCertifiedClassifier)
    (lipschitzConst : ℝ) (_hL : 0 < lipschitzConst) : ℝ :=
  c.entropyMargin / lipschitzConst



/-! ## Section 8: Entropy Power Inequality Structure

Bridge: connects InformationTheory (Shannon theory) to Physics (entropy power). -/

/-- Entropy power: e^(2H/n) for n-dimensional distributions.
    Bridge: connects InformationTheory to Physics (thermodynamic entropy). -/
def entropyPower (entropy_val : ℝ) (dimension : ℕ) (_hd : 0 < dimension) : ℝ :=
  Real.exp (2 * entropy_val / dimension)



/-! ## Section 9: Cross-Domain Security-Entropy-Robustness Triangle

This section establishes that cryptographic security, information entropy,
and ML robustness form a triangle of mutual reinforcement.
Bridge: connects Cryptography to InformationTheory to MachineLearning. -/

/-- The security-entropy-robustness triangle: a unified structure capturing
    the three-way relationship between security margin, entropy gap, and
    robustness radius. All three are proportional.
    Bridge: connects Cryptography to InformationTheory to MachineLearning. -/
structure SecurityEntropyRobustnessTriangle where
  /-- Security margin (bits) -/
  securityMargin : ℝ
  /-- Entropy gap (nats) -/
  entropyGap : ℝ
  /-- Robustness radius -/
  robustnessRadius : ℝ
  /-- All three are non-negative -/
  security_nonneg : 0 ≤ securityMargin
  gap_nonneg : 0 ≤ entropyGap
  radius_nonneg : 0 ≤ robustnessRadius
  /-- Security is bounded by entropy gap (conversion factor log 2) -/
  security_le_gap : securityMargin ≤ entropyGap / Real.log 2


/-! ## Section 10: Complexity Separation Results

Bridge: connects Computation to Cryptography to InformationTheory. -/




/-- Kyber-512 lattice parameters: dimension 256, modulus 3329.
    Bridge: connects Cryptography (lattice_crypto) to InformationTheory. -/
def kyber512Params : LatticeSecurity where
  dimension := 256
  modulus := 3329
  dim_pos := by norm_num
  mod_gt_one := by norm_num

/-- Kyber-768 lattice parameters: dimension 384, modulus 3329.
    Bridge: connects Cryptography (lattice_crypto) to InformationTheory. -/
def kyber768Params : LatticeSecurity where
  dimension := 384
  modulus := 3329
  dim_pos := by norm_num
  mod_gt_one := by norm_num


end CryptographicEntropy


