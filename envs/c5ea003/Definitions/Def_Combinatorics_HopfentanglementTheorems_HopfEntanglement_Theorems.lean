-- Prove2me | Definitions.Def_Combinatorics_HopfentanglementTheorems_HopfEntanglement_Theorems
-- name    : Combinatorics_HopfentanglementTheorems_HopfEntanglement_Theorems
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:48.746505+00:00
-- url     : https://prove2.me/theorems/ea4db709-9eee-4916-aaa1-56fa82da6ca8
-- title:
--   Aether Catalog definitions — Combinatorics_HopfentanglementTheorems_HopfEntanglement_Theorems
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.HopfentanglementTheorems.HopfEntanglement.Theorems`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/HopfentanglementTheorems/HopfEntanglement_Theorems.lean by skeleton subtraction
import Mathlib

/-!
# Hopf fibration and two-qubit entanglement

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/HopfEntanglement/Theorems.lean`.  It is reconstructed
here as a self-contained development of the classical bridge between the **Hopf
fibration** `S³ → S²` and the **entanglement of a two-qubit state**.

Two strands are developed and then joined:

* the Hopf map `h(z, w) = (2 z w̄, |z|² - |w|²)` from `ℂ²` to `ℂ × ℝ` satisfies
  `‖h(z,w)‖² = (|z|² + |w|²)²` (`HopfEntanglement.hopf_norm_sq`), so it maps the
  unit `3`-sphere onto the unit `2`-sphere, and it is invariant under the diagonal
  circle action (`HopfEntanglement.hopf_phase_invariant`) — the fibres are circles;
* a two-qubit state `(a, b, c, d)` is a product state exactly when its
  *concurrence determinant* `a*d - b*c` vanishes
  (`HopfEntanglement.isProduct_iff_det_eq_zero`);
* the bridge: for a **product** state the Hopf image of the first qubit's
  amplitudes is a genuine point of the Bloch sphere of that qubit, and the
  determinant obstruction is exactly the failure of the two Hopf projections to
  determine the state (`HopfEntanglement.product_hopf_factorization`).
-/

namespace HopfEntanglement

open Complex

/-! ## The Hopf map -/

/-- The Hopf map `ℂ² → ℂ × ℝ`, `h(z, w) = (2 z w̄, |z|² - |w|²)`. -/
def hopf (z w : ℂ) : ℂ × ℝ := (2 * z * (starRingEnd ℂ) w, Complex.normSq z - Complex.normSq w)





/-! ## Two-qubit states -/

/-- A two-qubit state, in the computational basis
`a|00⟩ + b|01⟩ + c|10⟩ + d|11⟩`. -/
structure TwoQubit where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ

/-- A state is a **product state** if it factors as a tensor product of one-qubit
states. -/
def IsProduct (s : TwoQubit) : Prop :=
  ∃ u₀ u₁ v₀ v₁ : ℂ, s.a = u₀ * v₀ ∧ s.b = u₀ * v₁ ∧ s.c = u₁ * v₀ ∧ s.d = u₁ * v₁

/-- The **concurrence determinant** `ad - bc`; up to a factor of `2` its modulus is
the concurrence of the state. -/
def det (s : TwoQubit) : ℂ := s.a * s.d - s.b * s.c


/-! ## The bridge -/




end HopfEntanglement


