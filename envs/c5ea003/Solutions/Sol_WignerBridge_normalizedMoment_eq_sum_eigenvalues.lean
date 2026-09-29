-- Prove2me | solution 1 for WignerBridge.normalizedMoment_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:20:21.142973+00:00
-- url     : https://prove2.me/submissions/d5015ed3-ce27-4a33-a79c-21e2a4230381

-- Sol generated from Probability/WignerTraceBridge.lean
import Mathlib
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_WignerBridge_normalizedMoment_eq
import Theorems.Thm_WignerBridge_trace_pow_eq_sum_eigenvalues_real
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
theorem solution{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    normalizedMoment A k =
      (1 / (Fintype.card n : ℝ)) *
        ∑ i, (hA.eigenvalues i / Real.sqrt (Fintype.card n)) ^ k := by
  rw [normalizedMoment_eq, trace_pow_eq_sum_eigenvalues_real hA k, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_pow]
  field_simp
  rw [div_pow, one_pow]
  ring
