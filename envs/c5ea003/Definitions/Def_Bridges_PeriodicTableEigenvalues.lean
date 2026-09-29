-- Prove2me | Definitions.Def_Bridges_PeriodicTableEigenvalues
-- name    : Bridges_PeriodicTableEigenvalues
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:06.271415+00:00
-- url     : https://prove2.me/theorems/c3a8bafd-256d-442e-956b-05c37fcbc269
-- title:
--   Aether Catalog definitions — Bridges_PeriodicTableEigenvalues
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PeriodicTableEigenvalues`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PeriodicTableEigenvalues.lean by skeleton subtraction
import Mathlib
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

namespace PeriodicTableEigenvalues

/-- The atomic number of the `i`-th element (`1`-indexed), as a real scalar. -/
def atomicNumber (n : ℕ) (i : Fin n) : ℝ := (i : ℝ) + 1

/-- The *nuclear Hamiltonian*: the diagonal operator whose spectrum is the
periodic table of the first `n` elements. -/
noncomputable def nuclearHamiltonian (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (atomicNumber n)

/-- The Hamiltonian as an endomorphism of the Hilbert space `Fin n → ℝ`. -/
noncomputable def H (n : ℕ) : Module.End ℝ (Fin n → ℝ) :=
  Matrix.toLin' (nuclearHamiltonian n)












end PeriodicTableEigenvalues


