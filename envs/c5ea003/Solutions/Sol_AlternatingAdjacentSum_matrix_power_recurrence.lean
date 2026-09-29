-- Prove2me | solution 1 for AlternatingAdjacentSum.matrix_power_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:12:47.53612+00:00
-- url     : https://prove2.me/submissions/9e81606c-1e8e-4d38-9c57-6af83c9cb743

-- Sol generated from Cryptography/AlternatingAdjacentSum.lean
import Mathlib
import Definitions.Def_Cryptography_AlternatingAdjacentSum
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Alternating adjacent-sum transfer matrices

This file formalizes the algebraic mechanism behind the parity split for
period-two adjacent-sum constraints.  A bound `b` is represented by its finite
zero-one compatibility matrix.  Pairing two successive bounds gives a single
transfer matrix.  Cayley--Hamilton in dimension two then shows that open
boundary counts and both cyclic parity classes obey the same second-order
recurrence, hence have a common quadratic denominator.
-/

open Finset BigOperators

open AlternatingAdjacentSum






/-- Cayley--Hamilton written entrywise for a two-state transfer matrix. -/
theorem two_state_cayley_hamilton {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) :
    M * M - (Matrix.trace M) • M + (Matrix.det M) • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two] <;> ring









open AlternatingAdjacentSum in
theorem solution{R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    M ^ (n + 2) = (Matrix.trace M) • M ^ (n + 1) - (Matrix.det M) • M ^ n := by
  have hc : M * M = (Matrix.trace M) • M - (Matrix.det M) • 1 := by
    rw [eq_sub_iff_add_eq]
    have h := two_state_cayley_hamilton M
    rw [← sub_eq_zero]
    convert h using 1
    abel
  rw [show M ^ (n + 2) = M ^ n * (M * M) by
    simp [pow_succ, Matrix.mul_assoc]]
  rw [hc, Matrix.mul_sub, Matrix.mul_smul]
  ext i j
  simp [pow_succ]
