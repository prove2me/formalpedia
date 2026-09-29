-- Prove2me | Theorems.Thm_InformationGeometry_klDiv_le_fisher
-- name    : InformationGeometry.klDiv_le_fisher
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:37.614129+00:00
-- url     : https://prove2.me/theorems/2cae647f-d2ef-4ed3-9223-db266b2ceec9
-- title:
--   The global information-geometric bridge: KL divergence is bounded above by
-- statement:
--   The global information-geometric bridge: KL divergence is bounded above by
--   Fisher squared displacement (equivalently, Pearson chi-squared divergence).
--
--   ```lean
--   theorem InformationGeometry.klDiv_le_fisher(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
--       (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
--       klDiv p q ≤ fisherForm q (p - q) (p - q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InformationGeometry/FisherMetric.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InformationGeometry/FisherMetric.lean#L140

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

theorem InformationGeometry.klDiv_le_fisher(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    klDiv p q ≤ fisherForm q (p - q) (p - q) := by sorry
