-- Prove2me | solution 1 for HopfEntanglement.hopf_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:43:23.936386+00:00
-- url     : https://prove2.me/submissions/0f4425bb-1deb-44c3-bc5f-691f63d0f597

-- Sol generated from Combinatorics/HopfentanglementTheorems/HopfEntanglement_Theorems.lean
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





/-! ## The bridge -/





open HopfEntanglement in
theorem solution(z w u : ℂ) (hu : Complex.normSq u = 1) :
    hopf (u * z) (u * w) = hopf z w := by
  have hconj : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj]
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hu
  refine Prod.ext ?_ ?_
  · show 2 * (u * z) * (starRingEnd ℂ) (u * w) = 2 * z * (starRingEnd ℂ) w
    rw [map_mul]
    calc 2 * (u * z) * ((starRingEnd ℂ) u * (starRingEnd ℂ) w)
        = (u * (starRingEnd ℂ) u) * (2 * z * (starRingEnd ℂ) w) := by ring
      _ = 2 * z * (starRingEnd ℂ) w := by rw [hconj, one_mul]
  · show Complex.normSq (u * z) - Complex.normSq (u * w)
        = Complex.normSq z - Complex.normSq w
    rw [Complex.normSq_mul, Complex.normSq_mul, hu, one_mul, one_mul]
