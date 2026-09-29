-- Prove2me | solution 1 for WignerBridge.trace_pow_eq_sum_eigenvalues_real
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:04.494675+00:00
-- url     : https://prove2.me/submissions/ae8ae387-302a-4f1c-9cd3-a5f40b7772b4

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

/-- **Trace–eigenvalue bridge.**  For a Hermitian matrix, the trace of the `k`-th
power is the `k`-th power sum of the eigenvalues. -/
theorem trace_pow_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : 𝕜)) ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  have h1 : (star hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 := by
    simp
  rw [h1, Matrix.one_mul, diagonal_pow, Matrix.trace_diagonal]
  simp








open WignerBridge in
theorem solution{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
  simpa using trace_pow_eq_sum_eigenvalues (𝕜 := ℝ) hA k
