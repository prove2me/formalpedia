-- Prove2me | solution 1 for LorentzianSmoothedAnalysis.quadFormBound_of_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:57:27.177131+00:00
-- url     : https://prove2.me/submissions/455532ee-1b78-4e25-b4cd-da4d45075e4f

-- Sol generated from Bridges/HilbertSpace/LorentzianSmoothedAnalysis.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_LorentzianSmoothedAnalysis
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Lorentzian Condition Numbers and Smoothed Analysis

This file establishes the first formal bridge from Lorentzian polynomial recognition
to smoothed analysis in the Spielman–Teng sense. We prove that Lorentzianity is not
merely structurally stable under perturbation, but **statistically stable** under noise:
the failure probability of Lorentzian signature preservation is controlled by an
exponential tail bound governed by the spectral gap.

## Mathematical Context

A Lorentzian polynomial (Brändén–Huh, 2020) has the property that all its quadratic
leaf Hessians have at most one positive eigenvalue. The spectral gap `ε` quantifies
how robustly this signature condition holds: on the orthogonal complement of a
witnessing direction, the quadratic form satisfies `Q_A(v) ≤ -ε·‖v‖²`.

The key conceptual chain is:
1. **Deterministic stability**: spectral gap `ε` gives a perturbation radius `ε`.
2. **Failure containment**: signature failure implies perturbation norm ≥ ε.
3. **Smoothed transfer**: any perturbation model with norm-tail bound yields
   a misclassification probability bound.

## Main Results

* `hasGappedSignature_signatureStable` — gap implies signature stability (Theorem 1)
* `conditionNumber_controls_radius` — condition number gives safe radius (Theorem 2)
* `failure_event_subset_gap_event` — failure ⊂ large-norm event (Theorem 3)
* `smoothed_failure_bound_abstract` — abstract smoothed analysis transfer (Theorem 3b)
* `gap_certificate_robust_tester` — one-sided robust tester (Theorem 4)
* `lorentzian_misclassification_norm_bound` — cross-domain bridge (Theorem 4b)

## Application Keywords

Lorentzian polynomial, spectral gap, smoothed analysis, condition number,
Gaussian perturbation, random matrix theory, operator norm tail bound,
robust recognition, algebraic combinatorics, average-case complexity,
phase transition, Hessian signature, numerical stability

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Spielman–Teng, "Smoothed Analysis of Algorithms", JACM, 2004
-/

open Finset BigOperators Matrix

noncomputable section

open LorentzianSmoothedAnalysis

/-! ## Core Definitions -/






/-! ## New Definitions for Smoothed Analysis -/







/-! ## Auxiliary Lemmas -/




/-! ## Theorem 1: Deterministic Spectral-Gap Preservation of Lorentzian Signature

**Mathematical statement.** If A has a gapped Lorentzian signature with spectral gap ε,
then every perturbation E with quadratic form bound ≤ ε preserves the Lorentzian
signature (at most one positive eigenvalue).

The proof: on w⊥, Q_{A+E}(v) = Q_A(v) + Q_E(v) ≤ -ε·‖v‖² + ε·‖v‖² = 0. -/






/-! ## Theorem 2: Condition Number Controls Safe Perturbation Radius

The condition number κ = maxNorm / minGap. Perturbations with quadratic
form bound ≤ minGap preserve the Lorentzian signature on all certificates. -/




/-! ## Theorem 3: Abstract Smoothed-Analysis Transfer Theorem

The set of perturbations that destroy the Lorentzian signature is contained
in the set where the gap failure event occurs. -/



/-
**Monotonicity of failure sets.** If ε₁ ≤ ε₂, then the gap failure event
    at level ε₂ implies the gap failure event at level ε₁.
    (Equivalently, if you can bound at ε₁, you can bound at any ε₂ ≥ ε₁.)
-/


/-! ## Monotonicity of the smoothed bound in gap and noise -/



/-! ## Theorem 4: Cross-Domain Bridge — Robust One-Sided Tester

A gap certificate yields a robust one-sided Lorentzian tester. -/



/-! ## Theorem 5: Stability Radius Existence -/


/-! ## Theorem 6: Composition of Perturbation Bounds -/



/-! ## Theorem 7: Gap Degradation is Additive -/


/-! ## Theorem 8: Uniform Gap Implies Uniform Stability -/


/-! ## Theorem 9: Entry-Bound to QuadForm Bound Bridge -/


/-! ## Theorem 10: Negative Definite Matrices Have Large Gap -/



/-! ## Theorem 11: Smoothed Condition Monotonicity

Note: `LorentzianSmoothedCondition κ ε σ` says `ε/σ ≤ κ`. Increasing ε makes the
ratio larger, so the correct monotonicity for gap is: a *smaller* gap ε makes the
condition easier to satisfy (weakening). For noise, increasing σ makes ε/σ smaller,
which makes the condition easier. -/



/-! ## Theorem 12: Scale Invariance of Condition Number

The Lorentzian condition number is scale-invariant: scaling
all certificate matrices by a positive constant doesn't change it. -/


/-! ## Conjecture (Lorentzian Smoothed Gap Law)

For degree-d homogeneous polynomials whose Lorentzian certificate matrix has
spectral gap ε > 0, and for Gaussian coefficient perturbations of variance σ²,
the misclassification probability satisfies
    Pr[Lorentzian misclassification] ≤ C exp(-c ε²/(n σ²))
for universal constants c, C > 0 depending at most on normalization.

**Testable prediction**: For fixed n, plotting log(failure probability)
against ε²/σ² should produce approximately linear decay with negative slope.

**Alternative hypotheses**:
- The correct parameter is stable rank rather than n.
- The relevant gap is derivative-stratified rather than the minimum eigenvalue gap.
- The decay rate depends on ε/σ (not ε²/σ²) for sparse polynomials.
-/


open LorentzianSmoothedAnalysis in
theorem solution    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ i j, |A i j| ≤ B) :
    QuadFormBound A ((n : ℝ) ^ 2 * B) := by
  intro v
  have h_sum : |QuadForm A v| ≤ B * ∑ i, ∑ j, |v i| * |v j| := by
    -- Apply the triangle inequality to the sum.
    have h_triangle : |QuadForm A v| ≤ ∑ i, ∑ j, |A i j| * |v i| * |v j| := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j _ => by rw [ ← abs_mul, ← abs_mul ] );
    exact h_triangle.trans ( by simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hentry i j ) ( abs_nonneg _ ) ) ( abs_nonneg _ ) );
  -- By AM-GM, |v(i)||v(j)| ≤ (v(i)²+v(j)²)/2. So ∑ᵢ ∑ⱼ |v(i)||v(j)| ≤ ∑ᵢ ∑ⱼ (v(i)²+v(j)²)/2 = n · ‖v‖².
  have h_am_gm : ∑ i, ∑ j, |v i| * |v j| ≤ n * ∑ i, v i ^ 2 := by
    have := Finset.univ.sum_le_sum fun i _ => Finset.univ.sum_le_sum fun j _ => show |v i| * |v j| ≤ ( v i ^ 2 + v j ^ 2 ) / 2 by nlinarith only [ sq_nonneg ( |v i| - |v j| ), abs_mul_abs_self ( v i ), abs_mul_abs_self ( v j ) ];
    simp_all +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_div ];
  rcases n with ( _ | n ) <;> simp_all +decide [ sqNorm ];
  nlinarith [ mul_le_mul_of_nonneg_left h_am_gm hB, show 0 ≤ ( n : ℝ ) * B * ∑ i, v i ^ 2 by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hB ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ]
