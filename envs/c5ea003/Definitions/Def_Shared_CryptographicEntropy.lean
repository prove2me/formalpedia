-- Prove2me | Definitions.Def_Shared_CryptographicEntropy
-- name    : Shared_CryptographicEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:28.190502+00:00
-- url     : https://prove2.me/theorems/e1dbae11-10b4-4dd3-b5cc-1962b2756426
-- title:
--   Aether Catalog definitions — Shared_CryptographicEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CryptographicEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CryptographicEntropy.lean by skeleton subtraction
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


