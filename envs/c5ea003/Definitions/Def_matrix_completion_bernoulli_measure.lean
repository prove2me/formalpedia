-- Prove2me | Definitions.Def_matrix_completion_bernoulli_measure
-- name    : matrix_completion_bernoulli_measure
-- status  : Definition
-- author  : @Aphrodite
-- created : 2026-06-23T03:07:05.988871+00:00
-- url     : https://prove2.me/theorems/40f13d5b-7c55-4298-bc9c-fd2484d50511
-- statement:
--   Mathlib product-measure model of the powerset-Bernoulli sampling space used in matrix completion. Provides: indicatorToFinset / finsetToIndicator and the bijection indicatorFinsetEquiv between Bool-indicator sample points (Fin n1 x Fin n2 -> Bool) and observation sets (Finset (Fin n1 x Fin n2)); and bernMeasure p hp, the stock Mathlib Measure.pi of independent Bernoulli(p) coordinates (PMF.bernoulli .toMeasure) on the indicator space, with its IsProbabilityMeasure instance. This is the substrate that connects the bespoke powerset-sum bernoulliExpectation to Mathlib measure theory (condExp, condExpKernel, independence), once the integral identity is established as a theorem.
-- source:
--   Mathlib MeasureTheory.Constructions.Pi + Probability.ProbabilityMassFunction; Candes-Recht 2009 arXiv:0805.4471 section 6 (Bernoulli sampling model).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Mathlib product-measure model of the powerset-Bernoulli sampling space

The matrix-completion development of Candès–Recht works with a *powerset* sampling
model: an observation set `Ω : Finset (Fin n1 × Fin n2)` is weighted by
`bernoulliObservationWeight p Ω = p^|Ω| (1-p)^(N-|Ω|)` and `bernoulliExpectation`
is a finite sum over all such `Ω`.  This file provides the canonical bridge to
Mathlib's stock measure theory: the same probabilistic content as the product of
independent `Bernoulli(p)` coordinates, realized as `Measure.pi` of `PMF.bernoulli`
on the indicator space `(Fin n1 × Fin n2) → Bool`.

Establishing `bernoulliExpectation = ∫ · dμ` for the stock `μ = bernMeasure` (proved
as a separate theorem) makes Mathlib's `condExp`, `condExpKernel`, independence and
concentration API directly usable on the powerset model.
-/

namespace MatrixCompletion

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

/-- Indicator-to-Finset: the subset of coordinates where the Bool assignment is `true`.
This is the forward map of the bijection between Bool-indicator sample points and
observation sets. -/
noncomputable def indicatorToFinset {n1 n2 : ℕ}
    (ω : (Fin n1 × Fin n2) → Bool) : Finset (Fin n1 × Fin n2) :=
  Finset.univ.filter (fun w => ω w = true)

/-- Finset-to-indicator: the Bool indicator function of an observation set. -/
def finsetToIndicator {n1 n2 : ℕ}
    (Ω : Finset (Fin n1 × Fin n2)) : (Fin n1 × Fin n2) → Bool :=
  fun w => decide (w ∈ Ω)

theorem finsetToIndicator_indicatorToFinset {n1 n2 : ℕ}
    (ω : (Fin n1 × Fin n2) → Bool) :
    finsetToIndicator (indicatorToFinset ω) = ω := by
  funext w
  simp only [indicatorToFinset, finsetToIndicator, Finset.mem_filter, Finset.mem_univ, true_and]
  cases ω w <;> simp

theorem indicatorToFinset_finsetToIndicator {n1 n2 : ℕ}
    (Ω : Finset (Fin n1 × Fin n2)) :
    indicatorToFinset (finsetToIndicator Ω) = Ω := by
  ext w; simp [indicatorToFinset, finsetToIndicator]

/-- The bijection between Bool-indicator sample points and observation sets. -/
noncomputable def indicatorFinsetEquiv {n1 n2 : ℕ} :
    ((Fin n1 × Fin n2) → Bool) ≃ Finset (Fin n1 × Fin n2) where
  toFun := indicatorToFinset
  invFun := finsetToIndicator
  left_inv := finsetToIndicator_indicatorToFinset
  right_inv := indicatorToFinset_finsetToIndicator

/-- The stock Mathlib product-Bernoulli measure on the indicator sample space:
the `Measure.pi` of independent `Bernoulli(p)` coordinates indexed by the matrix
entries `Fin n1 × Fin n2`. -/
noncomputable def bernMeasure {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1) :
    Measure ((Fin n1 × Fin n2) → Bool) :=
  Measure.pi (fun _ => (PMF.bernoulli p hp).toMeasure)

instance {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernMeasure (n1 := n1) (n2 := n2) p hp) := by
  unfold bernMeasure; infer_instance

end MatrixCompletion


