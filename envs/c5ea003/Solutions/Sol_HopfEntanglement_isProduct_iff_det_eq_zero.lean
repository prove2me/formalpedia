-- Prove2me | solution 1 for HopfEntanglement.isProduct_iff_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:43:24.509519+00:00
-- url     : https://prove2.me/submissions/40cafca0-c06f-4ebe-b1b3-5aa362fe9d56

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
theorem solution(s : TwoQubit) : IsProduct s ↔ det s = 0 := by
  constructor
  · rintro ⟨u₀, u₁, v₀, v₁, h1, h2, h3, h4⟩
    simp only [det, h1, h2, h3, h4]
    ring
  · intro hdet
    simp only [det, sub_eq_zero] at hdet
    by_cases ha : s.a = 0
    · by_cases hb : s.b = 0
      · -- the first row vanishes: take the first factor to be `(0, 1)`
        exact ⟨0, 1, s.c, s.d, by simp [ha], by simp [hb], by ring, by ring⟩
      · -- `b ≠ 0` and `a = 0` force `c = 0`, so the first column vanishes
        have hc : s.c = 0 := by
          have hbc : s.b * s.c = 0 := by rw [← hdet, ha, zero_mul]
          exact (mul_eq_zero.mp hbc).resolve_left hb
        exact ⟨s.b, s.d, 0, 1, by simp [ha], by ring, by simp [hc], by ring⟩
    · -- `a ≠ 0`: factor using the first column
      refine ⟨1, s.c / s.a, s.a, s.b, by ring, by ring, by field_simp, ?_⟩
      field_simp
      linear_combination hdet
