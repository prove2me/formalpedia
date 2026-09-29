-- Prove2me | Theorems.Thm_SheafCohomologyRobustness_GraphNerve_endpt_append
-- name    : SheafCohomologyRobustness.GraphNerve.endpt_append
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:52:42.105726+00:00
-- url     : https://prove2.me/theorems/5f39fae2-425e-4912-8325-41e4fd273606
-- title:
--   Endpt append
-- statement:
--   Formal statement of `SheafCohomologyRobustness.GraphNerve.endpt_append` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SheafCohomologyRobustness.GraphNerve.endpt_append(i : ι) (l₁ l₂ : List ι) :
--       endpt i (l₁ ++ l₂) = endpt (endpt i l₁) l₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/SheafCohomologyRobustness/GraphNervePoincare.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/SheafCohomologyRobustness/GraphNervePoincare.lean#L94

-- Thm stub generated from MachineLearning/SheafCohomologyRobustness/GraphNervePoincare.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Discrete Poincaré Lemma for Nerve Graphs, with Module Coefficients

This file generalises `SheafCohomologyRobustness.Cohomology` (path nerve and cyclic
nerve, real coefficients) to an **arbitrary nerve graph with coefficients in an
arbitrary abelian group**, and proves the exact obstruction theorem:

> `H¹(nerve, M) ∋ [c] = 0` **iff** every closed walk of the nerve has vanishing
> holonomy `∑ c`.

Concretely, for a symmetric adjacency relation `A` on a connected index type `ι`
of cover regions and an antisymmetric overlap discrepancy `c : ι → ι → M`
(a Čech `1`-cochain of the nerve):

* `cycleConsistent_of_isCoboundary` — a coboundary has zero holonomy on every
  closed walk (necessity);
* `isCoboundary_of_cycleConsistent` — conversely, zero holonomy on every closed
  walk produces an explicit **global potential** `f` with `c i j = f j - f i`
  (sufficiency, by transporting along chosen walks from a base region);
* `discrete_poincare_lemma` — the resulting iff, i.e. the exact computation of
  the vanishing locus of the first cohomology class of `c`.

The quantitative half turns this into certified robustness:

* `abs_wsum_le` — holonomy along a walk of length `k` with per-overlap
  discrepancy `≤ ε` is at most `k * ε`;
* `potential_spread_le` — the glued global certificate is `ε`-Lipschitz for the
  nerve graph distance;
* `glued_certified_radius_lower_bound` — if the nerve has diameter `≤ D` and all
  local certified radii agree up to `ε` on each overlap, then **every** region's
  certified radius is at least `r i₀ - D * ε`: a global certified `L∞` radius
  obtained purely from vanishing cohomology plus local data.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): the cycle/path dichotomy of the previous cycle is a
  shadow of a single theorem — for *any* nerve graph, the coboundary obstruction
  is exactly the family of closed-walk holonomies, with coefficients in any
  abelian group (not just `ℝ`).
* Experiment (Experimenter): the walk formalism `wsum / endpt / IsWalk / revW`
  (walk = base point + list of successors) made the append and reversal lemmas
  one-line inductions; the standard `List.Chain` API forced awkward endpoint
  bookkeeping and was abandoned after two attempts.
* Analysis (Analyst): the key structural step is `wsum_revW`, the statement that
  reversing a walk negates its holonomy — this is exactly where antisymmetry of
  the `1`-cochain (the Čech alternating condition) enters; without it the
  theorem is false, and the surviving statement is only the "necessity" half.
* Critique (Critic): `isCoboundary_of_cycleConsistent` is not vacuous — the
  hypothesis `CycleConsistent` is satisfiable and nontrivial (it holds for every
  coboundary by `cycleConsistent_of_isCoboundary`, and fails for the loop nerve
  cochain of `Cohomology.cyclic_not_coboundary`).
* Synthesis (PI): one theorem now subsumes the path (`H¹ = 0`) and loop
  (`H¹ ≠ 0`) computations and upgrades them to quantitative certificates.
-/


open SheafCohomologyRobustness
open GraphNerve

variable {ι : Type*} {M : Type*} [AddCommGroup M]

/-! ## §1. Walks in a nerve graph and holonomy of a `1`-cochain -/

theorem SheafCohomologyRobustness.GraphNerve.endpt_append(i : ι) (l₁ l₂ : List ι) :
    endpt i (l₁ ++ l₂) = endpt (endpt i l₁) l₂ := by sorry
