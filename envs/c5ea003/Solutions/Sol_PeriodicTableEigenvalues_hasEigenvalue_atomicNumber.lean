-- Prove2me | solution 1 for PeriodicTableEigenvalues.hasEigenvalue_atomicNumber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:27:29.723197+00:00
-- url     : https://prove2.me/submissions/37641505-91f0-4bee-846a-5beb996d1cf0

-- Sol generated from Bridges/PeriodicTableEigenvalues.lean
import Mathlib
import Definitions.Def_Bridges_PeriodicTableEigenvalues
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The Periodic Table Is a Lie: Elements as Eigenvalues

A cross-domain *connector* bridging **spectral / linear algebra** (self-adjoint
operators, eigenvalues, trace, determinant, characteristic polynomial) with
**elementary number theory** (triangular numbers `n(n+1)/2`, factorials `n!`).

## The construction

Mendeleev arranges the elements by atomic number `Z`.  We reinterpret the
periodic table spectrally: define the *nuclear Hamiltonian* as the diagonal
operator on the `n`-dimensional real Hilbert space `Fin n → ℝ` whose diagonal
entries are the atomic numbers `1, 2, …, n`.

## Main results

* `nuclearHamiltonian_isHermitian` — the Hamiltonian is self-adjoint (a genuine
  quantum-mechanical observable).
* `hasEigenvalue_atomicNumber` / `eigenvalue_imp_atomicNumber` /
  `spectrum_eq_range` — its spectrum is **exactly** the set of atomic numbers:
  the periodic table *is* the spectrum of an operator.
* `range_atomicNumber` — those eigenvalues are precisely the integers `1, …, n`.
* `trace_nuclearHamiltonian` — **spectral ↔ arithmetic bridge**: the trace (sum
  of eigenvalues) equals the Gauss triangular number `n(n+1)/2`.
* `trace_pow_nuclearHamiltonian` — **power-sum ladder**: the trace of the `k`-th
  power of the Hamiltonian equals the `k`-th power sum of the atomic numbers.
* `det_nuclearHamiltonian` — **spectral ↔ arithmetic bridge**: the determinant
  (product of eigenvalues) equals `n!`.
* `charpoly_nuclearHamiltonian` — the characteristic polynomial factors into
  linear terms rooted at the atomic numbers.
-/

open Matrix Module.End Polynomial

open PeriodicTableEigenvalues
















open PeriodicTableEigenvalues in
theorem solution(n : ℕ) (i : Fin n) :
    Module.End.HasEigenvalue (H n) (atomicNumber n i) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single i 1)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext j
    simp only [H, nuclearHamiltonian, Matrix.toLin'_apply, Matrix.mulVec_diagonal,
      Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne j i with h | h
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · intro hc
    have := congrFun hc i
    simp at this
