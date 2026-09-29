-- Prove2me | Definitions.Def_Tropical_DecomposableVerification_BlockGluing
-- name    : Tropical_DecomposableVerification_BlockGluing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:58.226112+00:00
-- url     : https://prove2.me/theorems/76990b64-a58b-4bbd-a699-4c46ac5e3776
-- title:
--   Aether Catalog definitions — Tropical_DecomposableVerification_BlockGluing
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.DecomposableVerification.BlockGluing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/DecomposableVerification/BlockGluing.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.

# Block Diagonal Matrix Verification — Sheaf-Style Gluing

## Overview

This file establishes the structural pillar of decomposable verification:
matrix identity verification for block-diagonal matrices reduces to
independent verification of each block.

## Main Results

* `block_diagonal_mul_eq_iff` — Block diagonal product equals block diagonal
  iff each block product equals the corresponding block.
* `block_diagonal_eq_zero_iff` — Block diagonal matrix is zero iff each block is zero.
* `block_diagonal_failure_detection` — Global block failure implies local block failure.
* `block_diagonal_mulVec_components` — mulVec on block diagonal reduces to
  local mulVec applications.
* `layerEval` / `networkEval` — Neural layer and block network evaluation.
* `linear_layer_certificate` — mulVec agreement implies layer output agreement.
* `block_network_certificate` — Local mulVec agreement implies global network agreement.
-/

open Matrix Finset

/-! ## Block Diagonal Multiplication Gluing -/





/-! ## Layer Certificate Infrastructure -/

/-- Simple linear layer evaluation via matrix-vector product. -/
noncomputable def layerEval {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  W.mulVec x


/-- Network evaluation on block-diagonal layers. -/
noncomputable def networkEval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix (n × ι) (n × ι) ℝ) (x : n × ι → ℝ) :
    n × ι → ℝ :=
  M.mulVec x


/-! ## Block Diagonal Subtraction and Discrepancy -/


