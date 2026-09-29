-- Prove2me | Theorems.Thm_InformationGeometry_klDiv_nonneg
-- name    : InformationGeometry.klDiv_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:40.664286+00:00
-- url     : https://prove2.me/theorems/82cd6c86-3f73-413e-baa7-08afc44f5300
-- title:
--   Gibbs' inequality: relative entropy is nonnegative.
-- statement:
--   Gibbs' inequality: relative entropy is nonnegative.
--
--   ```lean
--   theorem InformationGeometry.klDiv_nonneg(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
--       (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
--       0 ≤ klDiv p q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InformationGeometry/FisherMetric.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InformationGeometry/FisherMetric.lean#L121

-- Thm stub generated from Bridges/InformationGeometry/FisherMetric.lean
import Mathlib
import Definitions.Def_Bridges_InformationGeometry_FisherMetric

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

open InformationGeometry

variable {ι : Type*} [Fintype ι]

theorem InformationGeometry.klDiv_nonneg(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    0 ≤ klDiv p q := by sorry
