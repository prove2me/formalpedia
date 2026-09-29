-- Prove2me | Theorems.Thm_HopfEntanglement_isProduct_iff_det_eq_zero
-- name    : HopfEntanglement.isProduct_iff_det_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:18:31.758131+00:00
-- url     : https://prove2.me/theorems/a56ee752-4425-4243-9abb-1d53252de956
-- title:
--   Entanglement criterion.
-- statement:
--   **Entanglement criterion.**  A two-qubit state is a product state exactly when
--   its concurrence determinant vanishes.
--
--   ```lean
--   theorem HopfEntanglement.isProduct_iff_det_eq_zero(s : TwoQubit) : IsProduct s ↔ det s = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/HopfentanglementTheorems/HopfEntanglement_Theorems.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/HopfentanglementTheorems/HopfEntanglement_Theorems.lean#L100

-- Thm stub generated from Combinatorics/HopfentanglementTheorems/HopfEntanglement_Theorems.lean
import Mathlib
import Definitions.Def_Combinatorics_HopfentanglementTheorems_HopfEntanglement_Theorems

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

open HopfEntanglement

open Complex

/-! ## The Hopf map -/






/-! ## Two-qubit states -/

theorem HopfEntanglement.isProduct_iff_det_eq_zero(s : TwoQubit) : IsProduct s ↔ det s = 0 := by sorry
