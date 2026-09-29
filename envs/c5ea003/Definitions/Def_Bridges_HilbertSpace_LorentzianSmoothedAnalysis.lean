-- Prove2me | Definitions.Def_Bridges_HilbertSpace_LorentzianSmoothedAnalysis
-- name    : Bridges_HilbertSpace_LorentzianSmoothedAnalysis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:02.307391+00:00
-- url     : https://prove2.me/theorems/29b2c633-ea79-44a2-936c-513a57b02f61
-- title:
--   Aether Catalog definitions — Bridges_HilbertSpace_LorentzianSmoothedAnalysis
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HilbertSpace.LorentzianSmoothedAnalysis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HilbertSpace/LorentzianSmoothedAnalysis.lean by skeleton subtraction
import Mathlib
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

namespace LorentzianSmoothedAnalysis

/-! ## Core Definitions -/

/-- The quadratic form induced by a matrix A: Q_A(x) = ∑ᵢ ∑ⱼ A(i,j) x(i) x(j). -/
def QuadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- Squared Euclidean norm of a vector. -/
def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

/-- A matrix has "at most one positive eigenvalue" (Lorentzian signature) if there
    exists a direction w such that Q_A(v) ≤ 0 for all v orthogonal to w. -/
def HasAtMostOnePositiveEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∀ v : Fin n → ℝ,
    (∑ i, w i * v i = 0) → QuadForm A v ≤ 0

/-- **Gapped Lorentzian signature** with quantitative spectral gap ε.
    There exists a direction w such that Q_A(v) ≤ -ε·‖v‖² on w⊥. -/
def HasGappedSignature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∀ v : Fin n → ℝ,
    (∑ i, w i * v i = 0) → QuadForm A v ≤ -ε * sqNorm v

/-- A bound on the quadratic form of a matrix: |Q_A(v)| ≤ c · ‖v‖² for all v. -/
def QuadFormBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, |QuadForm A v| ≤ c * sqNorm v

/-! ## New Definitions for Smoothed Analysis -/

/-- **Gap failure event**: A perturbation E causes a gap failure when its
    quadratic form bound exceeds the spectral gap ε. -/
def GapFailureEvent {n : ℕ}
    (ε : ℝ) (E : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ¬QuadFormBound E ε

/-- **Signature-stable under perturbation radius δ**: A matrix A has stable
    Lorentzian signature under all perturbations with quadratic form bound < δ. -/
def SignatureStableUnder {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : Prop :=
  ∀ E : Matrix (Fin n) (Fin n) ℝ,
    QuadFormBound E δ →
    HasAtMostOnePositiveEigenvalue (A + E)

/-- **Lorentzian smoothed condition**: Abstract smoothed-condition surrogate. -/
def LorentzianSmoothedCondition (κ ε σ : ℝ) : Prop :=
  0 < ε ∧ 0 < σ ∧ ε / σ ≤ κ

/-- **Uniform gapped signature**: All matrices in a collection have gapped
    Lorentzian signature with the same gap ε. -/
def UniformGap {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Prop :=
  ∀ k, HasGappedSignature (As k) ε

/-- **Lorentzian condition number** for a collection of certificate matrices. -/
def LorentzianConditionNumber (minGap maxNorm : ℝ) : ℝ :=
  if minGap > 0 then maxNorm / minGap else 0

/-- **Robust tester result**: output of a robust Lorentzian tester. -/
structure RobustTesterResult where
  accepts : Bool
  safeRadius : ℝ
  safeRadius_pos : accepts = true → 0 < safeRadius

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

end LorentzianSmoothedAnalysis


