-- Prove2me | Definitions.Def_Probability_EMLInformationGeometry
-- name    : Probability_EMLInformationGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:21.122017+00:00
-- url     : https://prove2.me/theorems/a7659556-82a5-44b9-8b54-489c351a5b6b
-- title:
--   Aether Catalog definitions — Probability_EMLInformationGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.EMLInformationGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/EMLInformationGeometry.lean by skeleton subtraction
import Mathlib

/-!
# Fisher information of a normalized exp-log neuron

On a finite sample space, this file studies the normalized weights

`exp(a) * log(b * xᵢ + 1)`.

The common factor `exp(a)` cancels from the associated probability distribution.
Consequently the parameter `a` is not identifiable: its score vanishes, the
corresponding row and column of the Fisher matrix vanish, and the two-parameter
Fisher matrix is singular.  Thus this single-neuron family cannot carry a
nondegenerate two-dimensional Hessian metric, let alone a hyperbolic metric of
constant negative curvature, without changing the model or quotienting out the
redundant scale parameter.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace EMLInformationGeometry

variable {ι : Type*} [Fintype ι]

/-- The logarithmic activation of sample `i`. -/
def activation (x : ι → ℝ) (b : ℝ) (i : ι) : ℝ :=
  Real.log (b * x i + 1)

/-- The total logarithmic activation. -/
def activationMass (x : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ i, activation x b i

/-- The unnormalized exp-log weight of sample `i`. -/
def rawWeight (x : ι → ℝ) (a b : ℝ) (i : ι) : ℝ :=
  Real.exp a * activation x b i

/-- The partition function of the finite exp-log model. -/
def partition (x : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, rawWeight x a b i

/-- The normalized exp-log probability weight. -/
def probability (x : ι → ℝ) (a b : ℝ) (i : ι) : ℝ :=
  rawWeight x a b i / partition x a b








/-- The normalized score in the common scale direction.  The first term is the
logarithmic derivative of each raw weight and the second is that of the partition. -/
def scaleScore (x : ι → ℝ) (a b : ℝ) : ℝ :=
  1 - partition x a b / partition x a b


/-- The Fisher information in the exponential scale direction. -/
def fisherAA (x : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, probability x a b i * scaleScore x a b ^ 2


/-- The Fisher pairing between the scale score and an arbitrary second score. -/
def fisherScaleAgainst (x : ι → ℝ) (a b : ℝ) (score : ι → ℝ) : ℝ :=
  ∑ i, probability x a b i * scaleScore x a b * score i


/-- The two-parameter Fisher matrix, with the true scale score in coordinate zero
and an arbitrary candidate score for the shape parameter in coordinate one. -/
def fisherMatrix (x : ι → ℝ) (a b : ℝ) (shapeScore : ι → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun j k => ∑ i, probability x a b i *
    (if j = 0 then scaleScore x a b else shapeScore i) *
    (if k = 0 then scaleScore x a b else shapeScore i)

/-- The determinant of the two-parameter Fisher matrix. -/
def fisherDeterminant (x : ι → ℝ) (a b : ℝ) (shapeScore : ι → ℝ) : ℝ :=
  fisherMatrix x a b shapeScore 0 0 * fisherMatrix x a b shapeScore 1 1 -
    fisherMatrix x a b shapeScore 0 1 * fisherMatrix x a b shapeScore 1 0





end EMLInformationGeometry


