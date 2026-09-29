-- Prove2me | solution 1 for WignerBridge.normalizedMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:03.948596+00:00
-- url     : https://prove2.me/submissions/09bca39e-4609-459d-ae7e-60cb4679f401

-- Sol generated from Probability/WignerTraceBridge.lean
import Mathlib
import Definitions.Def_Probability_WignerTraceBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The trace–eigenvalue bridge for empirical spectral distributions

The moment method for the Wigner semicircle law rests on the identity

  (1/N) Σᵢ λᵢᵏ = (1/N) tr(Aᵏ),

which converts a statement about the *empirical spectral distribution* (ESD) of a
Hermitian matrix into a statement about traces of powers, i.e. into a sum over
closed walks in the complete graph.  This file proves that bridge for arbitrary
Hermitian matrices over an `RCLike` field, specialises it to the real symmetric
case, and sets up the `√N`-normalised spectral moments used in the semicircle law.
-/

open Matrix BigOperators

open WignerBridge

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]









open WignerBridge in
theorem solution(A : Matrix n n ℝ) (k : ℕ) :
    normalizedMoment A k =
      (1 / (Fintype.card n : ℝ)) * (Real.sqrt (Fintype.card n))⁻¹ ^ k * (A ^ k).trace := by
  rw [normalizedMoment, smul_pow, Matrix.trace_smul, smul_eq_mul]
  ring
