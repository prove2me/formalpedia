-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
-- name    : MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:37.3781+00:00
-- url     : https://prove2.me/theorems/7f1bed1f-3ea2-4422-8441-eba2a65200c9
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.GraphNervePoincare`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/GraphNervePoincare.lean by skeleton subtraction
import Mathlib
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


namespace SheafCohomologyRobustness
namespace GraphNerve

variable {ι : Type*} {M : Type*} [AddCommGroup M]

/-! ## §1. Walks in a nerve graph and holonomy of a `1`-cochain -/

/-- Holonomy of the `1`-cochain `c` along the walk that starts at `i` and visits
the vertices of `l` in order: `wsum c i [j, k] = c i j + c j k`. -/
def wsum (c : ι → ι → M) : ι → List ι → M
  | _, [] => 0
  | i, j :: t => c i j + wsum c j t

/-- Endpoint of the walk starting at `i` and visiting `l`. -/
def endpt : ι → List ι → ι
  | i, [] => i
  | _, j :: t => endpt j t

/-- `IsWalk A i l` says that every consecutive pair of `i :: l` is an edge of the
nerve graph `A` (i.e. the corresponding cover regions overlap). -/
def IsWalk (A : ι → ι → Prop) : ι → List ι → Prop
  | _, [] => True
  | i, j :: t => A i j ∧ IsWalk A j t

/-- The reversed walk: the successor list of the walk `i :: l` read backwards,
based at `endpt i l`. -/
def revW : ι → List ι → List ι
  | _, [] => []
  | i, j :: t => revW j t ++ [i]









/-! ## §2. Cocycle conditions and the discrete Poincaré lemma -/

/-- **Vanishing holonomy.**  Every closed walk of the nerve has zero total
discrepancy.  This is the "no adversarial loop" condition. -/
def CycleConsistent (A : ι → ι → Prop) (c : ι → ι → M) : Prop :=
  ∀ i l, IsWalk A i l → endpt i l = i → wsum c i l = 0

/-- `c` is a Čech coboundary on the nerve: the overlap discrepancies come from a
single global section `f` (a global certificate). -/
def IsCoboundaryOn (A : ι → ι → Prop) (c : ι → ι → M) : Prop :=
  ∃ f : ι → M, ∀ i j, A i j → c i j = f j - f i

/-- The nerve graph is connected: every region is reachable from every other
through a chain of overlaps. -/
def IsConnectedNerve (A : ι → ι → Prop) : Prop := ∀ i j, ∃ l, IsWalk A i l ∧ endpt i l = j






/-! ## §3. Quantitative gluing: certified `L∞` radii from vanishing cohomology -/




/-! ## §4. Tree nerves have vanishing `H¹`, for arbitrary coefficients -/

/-- A rooted-tree structure on the index type of a cover: every region has a
parent region it overlaps, and the parent is strictly closer to the root. -/
structure RootedTree (ι : Type*) where
  /-- The base region. -/
  root : ι
  /-- The parent region of each region. -/
  parent : ι → ι
  /-- Distance to the root. -/
  rank : ι → ℕ
  /-- Non-root regions are strictly further from the root than their parent. -/
  rank_parent : ∀ i, i ≠ root → rank (parent i) < rank i

/-- The nerve graph of a rooted tree of regions: `i` and `j` overlap when one is
the parent of the other. -/
def TreeAdj {ι : Type*} (T : RootedTree ι) (i j : ι) : Prop :=
  (T.parent i = j ∧ i ≠ T.root) ∨ (T.parent j = i ∧ j ≠ T.root)

/-- The potential obtained by integrating the overlap discrepancies from the root
down to each region along the unique tree path. -/
noncomputable def treePotential [DecidableEq ι] (T : RootedTree ι) (c : ι → ι → M)
    (i : ι) : M :=
  if _hne : i = T.root then 0 else treePotential T c (T.parent i) + c (T.parent i) i
termination_by T.rank i
decreasing_by exact T.rank_parent i ‹i ≠ T.root›




end GraphNerve
end SheafCohomologyRobustness


