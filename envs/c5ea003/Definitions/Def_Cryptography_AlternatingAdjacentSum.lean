-- Prove2me | Definitions.Def_Cryptography_AlternatingAdjacentSum
-- name    : Cryptography_AlternatingAdjacentSum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:02:47.691798+00:00
-- url     : https://prove2.me/theorems/c54753dc-8f26-472b-83ad-93f1dea99c96
-- title:
--   Aether Catalog definitions — Cryptography_AlternatingAdjacentSum
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AlternatingAdjacentSum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AlternatingAdjacentSum.lean by skeleton subtraction
import Mathlib
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

namespace AlternatingAdjacentSum

/-- The zero-one transfer matrix for the constraint `i + j ≤ b`. -/
def adjacencyMatrix (d b : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => if (i : ℕ) + (j : ℕ) ≤ b then 1 else 0

/-- The two-step transfer matrix for consecutive bounds `s` and `s+1`. -/
def periodMatrix (d s : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  adjacencyMatrix d s * adjacencyMatrix d (s + 1)

/-- A scalar obtained by imposing arbitrary left and right boundary weights on
`n` periods of a transfer matrix. -/
def openCount {R : Type*} [CommRing R] (u v : Fin 2 → R)
    (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : R :=
  ∑ i, ∑ j, u i * (M ^ n) i j * v j

/-- The even cyclic parity class is the trace after `n` complete periods. -/
def evenCyclicCount {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : R :=
  Matrix.trace (M ^ n)

/-- The odd cyclic parity class has one extra transfer step. -/
def oddCyclicCount {R : Type*} [CommRing R]
    (M A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : R :=
  Matrix.trace (M ^ n * A)









end AlternatingAdjacentSum


