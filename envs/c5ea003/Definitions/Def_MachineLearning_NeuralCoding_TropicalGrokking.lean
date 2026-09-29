-- Prove2me | Definitions.Def_MachineLearning_NeuralCoding_TropicalGrokking
-- name    : MachineLearning_NeuralCoding_TropicalGrokking
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:43.763985+00:00
-- url     : https://prove2.me/theorems/eed83d3f-91ce-447b-bfdf-c7b7f4458e2a
-- title:
--   Aether Catalog definitions — MachineLearning_NeuralCoding_TropicalGrokking
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NeuralCoding.TropicalGrokking`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NeuralCoding/TropicalGrokking.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Grokking: Phase Transitions in Piecewise-Linear Loss Landscapes

This file formalizes a mathematical framework connecting **delayed generalization
(grokking)** in neural networks with **tropical geometry**. The key insight is that
piecewise-linear loss landscapes naturally decompose into tropical cells (regions
where a fixed affine form achieves the minimum), and grokking corresponds to a
training trajectory crossing the boundary between cells — a **corner-locus crossing**.

## Mathematical Overview

We model class scores as **tropical polynomials** — finite minima of affine forms.
The parameter space decomposes into cells where the same affine form is active
(achieves the minimum). When a training trajectory crosses from one cell to another,
the combinatorial structure of the classifier changes discontinuously, even though
the loss may change continuously. This is the tropical-geometric mechanism for
grokking: delayed generalization is a **chamber transition** in the tropical
cell complex.

## Main Definitions

* `AffineForm` — An affine function on ℝⁿ, represented as (linear part, constant)
* `evalAffine` — Evaluation of an affine form
* `TropPoly` — Tropical polynomial: minimum of finitely many affine forms
* `activeSet` — The set of affine forms achieving the minimum at a point
* `isCornerCrossing` — Whether the active set changes between two points
* `marginFromScores` — Decision margin: gap between best and second-best class scores
* `degeneracyIndex` — Count of classes within δ of the decision boundary
* `chartStableOn` — Active set constancy along a trajectory segment
* `grokkingOnset` — Margin strictly increases at a trajectory step

## Main Results

* `cellwise_affinity` — On a fixed active cell, TropPoly equals a single affine form
* `tropical_grokking_jump` — A strict margin increase implies a quantitative gap
* `no_grokking_without_corner_crossing` — Constant active set ⟹ affine score evolution
* `degeneracy_drop_at_margin_jump` — Margin jump implies degeneracy decrease
* `corner_crossing_of_score_change` — Non-affine score change requires corner crossing

## References

* Noel, Power, Rudolph, "Grokking as a phase transition" (2022)
* Zhang, Mikhailiuk, "Tropical geometry of deep neural networks" (2018)
* Maragos, Charisopoulos, Theodosis, "Tropical geometry and machine learning" (2021)
-/

noncomputable section

open Finset

/-! ## Section 1: Core Definitions -/

/-- An affine form on ℝⁿ, represented as a pair (w, b) where w is the linear part
and b is the bias/constant term. Evaluates as ∑ᵢ wᵢxᵢ + b. -/
def AffineForm (n : ℕ) := (Fin n → ℝ) × ℝ

/-- Evaluate an affine form at a point x ∈ ℝⁿ. -/
def evalAffine {n : ℕ} (a : AffineForm n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, a.1 i * x i) + a.2

/-- A **tropical polynomial**: the minimum (infimum) of finitely many affine forms.
This is the fundamental building block of piecewise-linear functions arising
from ReLU neural networks and tropical geometry. -/
def TropPoly {n m : ℕ} [NeZero m] (P : Fin m → AffineForm n) (x : Fin n → ℝ) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun i => evalAffine (P i) x)

/-- The **active set** at a point x: the collection of affine forms that achieve
the minimum value of the tropical polynomial at x. In tropical geometry, the
point lies on the corner locus when |activeSet| > 1. -/
def activeSet {n m : ℕ} [NeZero m] (P : Fin m → AffineForm n) (x : Fin n → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => evalAffine (P i) x = TropPoly P x)


/-- The **decision margin** for a classifier with score functions: the minimum
gap between the score of any competing class j and the true class y.
Positive margin means correct classification; larger margin means more robust. -/
def marginFromScores {k n : ℕ} (score : (Fin n → ℝ) → Fin k → ℝ)
    (y : Fin k) (x : Fin n → ℝ) (hk : 1 < k) : ℝ :=
  Finset.inf' ((Finset.univ : Finset (Fin k)).filter (· ≠ y))
    (by
      rw [Finset.filter_nonempty_iff]
      have : ∃ j : Fin k, j ≠ y := by
        by_contra h; push_neg at h
        have : Fintype.card (Fin k) ≤ 1 := Fintype.card_le_one_iff.mpr
          (fun a b => (h a).trans (h b).symm)
        simp at this; omega
      obtain ⟨j, hj⟩ := this
      exact ⟨j, Finset.mem_univ j, hj⟩)
    (fun j => score x j - score x y)

/-- The **degeneracy index**: counts how many competing classes have score
within δ of the true class score. High degeneracy means the classifier is
near the decision boundary for multiple classes simultaneously. -/
def degeneracyIndex {k n : ℕ}
    (score : (Fin n → ℝ) → Fin k → ℝ) (y : Fin k) (δ : ℝ)
    (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun j => j ≠ y ∧ score x j - score x y ≤ δ).card



/-! ## Section 2: Fundamental Lemmas -/

/-
The active set is always nonempty: at least one affine form achieves the minimum.
-/

/-
**Cellwise Affinity Lemma**: At any point x, every active affine form evaluates
to exactly the tropical polynomial value. This is the key property that makes
tropical cells "affine regions" of the piecewise-linear function.
-/

/-
Every affine form evaluates to at least the tropical polynomial value
(the tropical polynomial is the minimum).
-/

/-
TropPoly equals evalAffine of any active form (reverse direction of cellwise_affinity).
-/

/-! ## Section 3: Tropical Grokking Jump Theorem (Theorem A)

The central result: if the decision margin strictly increases at a trajectory step,
then the increase is quantitatively controlled — there exists a positive gap ε
witnessing the discontinuous improvement in classification confidence.

This is the formal seed for interpreting grokking as a tropical phase transition:
the margin jump is not gradual but discrete, forced by the combinatorial structure
of the tropical cell decomposition. -/

/-
**Tropical Grokking Jump Theorem**: If the margin strictly increases between
consecutive trajectory points, then there exists a quantitative gap ε > 0.
This captures the key phenomenon of grokking: generalization improves not
continuously but in discrete jumps corresponding to tropical cell transitions.
-/

/-! ## Section 4: No Grokking Without Corner Crossing (Theorem C)

If the active set remains constant along a trajectory, the tropical polynomial
is affine on that segment. Since an affine function changes smoothly and predictably,
no sudden generalization improvement (grokking) can occur. This theorem establishes
that **corner-locus crossing is necessary for grokking**. -/

/-
**No Grokking Without Corner Crossing**: If two points share the same active
element i, then the difference of TropPoly values equals the difference of the
i-th affine form values. Within a single tropical cell, the score function is
affine and changes predictably. Grokking — a *sudden* generalization improvement —
can only happen when the trajectory crosses the corner locus.
-/

/-! ## Section 5: Corner Crossing Detection

We prove that if the tropical polynomial value at two points differs by an amount
inconsistent with any single affine form, a corner crossing must have occurred. -/

/-
If the active sets at two points share a common element, then the TropPoly
difference equals the difference of that affine form.
-/

/-
**Corner Crossing from Score Change**: If the TropPoly difference between x₁ and x₂
is not equal to the difference of the i-th affine form (which was active at x₁),
then i is not active at x₂, witnessing a corner crossing.
-/

/-! ## Section 6: Order Parameter and Grokking Prediction (Theorem B)

The degeneracy index counts how many classes are within δ of the decision boundary.
We prove that a margin jump (all competitors pushed beyond δ) forces the degeneracy
to drop to zero. -/


/-
**Degeneracy Index Bounded**: The degeneracy index is at most k - 1
(the number of competing classes).
-/

/-
**Degeneracy Drops to Zero**: If all competitors have score strictly beyond δ
from the true class, the degeneracy index is zero.
-/

/-
**Degeneracy Positive with Near Competitor**: If some competitor has score
within δ of the true class, the degeneracy index is positive.
-/

/-
**Degeneracy Drop at Margin Jump**: If there exists a near competitor before
the transition but none after, the degeneracy index strictly decreases.
This is the formal connection: margin jump ⟹ degeneracy drop.
-/

/-
**Order Parameter Predicts Grokking (Theorem B)**: If the degeneracy index
drops along a trajectory and the link between zero degeneracy and large margin
holds, then there exists a point with large margin.

This formalizes the prediction: monitoring the tropical order parameter Φ
(degeneracy index) allows detecting grokking onset — a degeneracy drop
to zero guarantees that generalization margin exceeds δ for all competitors.
-/

/-! ## Section 7: Concrete Example

We provide a 2D example with 2 affine forms demonstrating active set change. -/

/-- Example: affine form f₁(x) = x₁ -/
def exForm1 : AffineForm 2 := (![1, 0], 0)
/-- Example: affine form f₂(x) = x₂ - 1 -/
def exForm2 : AffineForm 2 := (![0, 1], -1)

/-
At the point (2, 0), f₂(2,0) = -1 ≤ 2 = f₁(2,0),
so f₂ achieves the minimum.
-/

/-
At the point (0, 2), f₁(0,2) = 0 ≤ 1 = f₂(0,2),
so f₁ achieves the minimum.
-/

end


