-- Prove2me | solution 1 for SheafCohomologyRobustness.GraphNerve.endpt_revW
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:28:46.848208+00:00
-- url     : https://prove2.me/submissions/89b232cc-3555-4764-a2ab-ec815d3d7a87

-- Sol generated from MachineLearning/SheafCohomologyRobustness/GraphNervePoincare.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Theorems.Thm_SheafCohomologyRobustness_GraphNerve_endpt_append
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













/-! ## §2. Cocycle conditions and the discrete Poincaré lemma -/









/-! ## §3. Quantitative gluing: certified `L∞` radii from vanishing cohomology -/




/-! ## §4. Tree nerves have vanishing `H¹`, for arbitrary coefficients -/








open SheafCohomologyRobustness in
theorem solution(i : ι) (l : List ι) : endpt (endpt i l) (revW i l) = i := by
  induction l generalizing i with
  | nil => rfl
  | cons a t _ => simp [endpt, revW, endpt_append]
