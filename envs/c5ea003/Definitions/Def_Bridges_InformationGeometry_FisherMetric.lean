-- Prove2me | Definitions.Def_Bridges_InformationGeometry_FisherMetric
-- name    : Bridges_InformationGeometry_FisherMetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:54.906139+00:00
-- url     : https://prove2.me/theorems/bd4ca84e-b680-46fe-8301-e0c6779e7c4b
-- title:
--   Aether Catalog definitions — Bridges_InformationGeometry_FisherMetric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InformationGeometry.FisherMetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InformationGeometry/FisherMetric.lean by skeleton subtraction
import Mathlib

/-!
# The Fisher metric on the finite statistical manifold

We model the open probability simplex on a finite type `ι`.  At a positive
probability vector `p`, tangent vectors are functions `ι → ℝ` (the Fisher form
restricts in particular to the usual zero-sum tangent hyperplane).

The file builds a chain from the score representation of Fisher information,
through all algebraic and positivity axioms of a real inner product, to a global
information-geometric comparison

`0 ≤ KL(p ‖ q) ≤ g_q(p - q, p - q)`.

Thus the local quadratic geometry is explicitly connected to statistical
relative entropy.  No analytic limiting assumptions are needed for this finite,
strictly positive model.
-/

noncomputable section

open Finset

namespace InformationGeometry

variable {ι : Type*} [Fintype ι]

/-- The Fisher information form of a finite categorical model. -/
def fisherForm (p v w : ι → ℝ) : ℝ :=
  ∑ i, v i * w i / p i

/-- Kullback--Leibler divergence on a finite categorical model. -/
def klDiv (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- Pearson's chi-squared divergence. -/
def chiSquared (p q : ι → ℝ) : ℝ :=
  ∑ i, (p i - q i) ^ 2 / q i















end InformationGeometry

end


