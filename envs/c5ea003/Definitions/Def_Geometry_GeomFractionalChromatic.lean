-- Prove2me | Definitions.Def_Geometry_GeomFractionalChromatic
-- name    : Geometry_GeomFractionalChromatic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:16:52.903743+00:00
-- url     : https://prove2.me/theorems/42d6b289-bd54-4b95-b627-16b9766cb207
-- title:
--   Aether Catalog definitions — Geometry_GeomFractionalChromatic
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GeomFractionalChromatic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GeomFractionalChromatic.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. All rights reserved.

# Geometric Fractional Chromatic Number: the independence-ratio engine

This file develops, from first principles, the linear-programming lower bound that
drives the Matolcsi–Ruzsa–Varga–Zsámboki (`MRVZ`) programme on the fractional
chromatic number of the plane, following the strategy of de Grey (`deGrey`) and the
classical Erdős framing (`Er87`).

The *geometric fractional chromatic number* of a finite graph `G` is the value of the
covering linear program: assign nonnegative weights to the independent sets so that
every vertex is covered with total weight at least `1`, and minimise the total weight.
We model a feasible point as a `FracColoring` and define `geomFrac G` as the infimum of
the achievable totals.

## Main results

* `FracColoring.card_le_indepNum_mul_total` — the LP-duality core:
  `|V| ≤ α(G) · total(c)` for every feasible fractional coloring `c`,
  where `α(G) = G.indepNum` is the independence number.  This is a genuine
  double-counting / weak-duality argument.
* `geomFrac_ge_ratio` — consequently `|V| / α(G) ≤ geomFrac G`.
* `geomFrac_gt_four_of_indep_ratio` — **the key technical mechanism**: if the
  independence ratio is below `1/4` (i.e. `4 · α(G) < |V|`), then
  `geomFrac G > 4`.  This is exactly the reduction used by `MRVZ`: a finite
  unit-distance graph with independence ratio `< 1/4` has fractional chromatic
  number strictly above `4`, hence so does the plane.
* `geomFrac_le_card` — the trivial singleton coloring gives `geomFrac G ≤ |V|`.

The geometric (unit-distance) instantiation lives in `UnitDistanceFractional.lean`.
-/

open SimpleGraph Finset
open scoped BigOperators

namespace GeomFrac

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A feasible point of the fractional-coloring covering LP for `G`:
nonnegative weights supported on independent sets, covering every vertex with
total weight at least `1`. -/
structure FracColoring (G : SimpleGraph V) where
  /-- Weight assigned to each finite set of vertices. -/
  weight : Finset V → ℝ
  /-- Weights are nonnegative. -/
  nonneg : ∀ S, 0 ≤ weight S
  /-- Only independent sets may carry positive weight. -/
  supp : ∀ S : Finset V, ¬ G.IsIndepSet (S : Set V) → weight S = 0
  /-- Every vertex is covered with total weight at least `1`. -/
  covers : ∀ v : V, 1 ≤ ∑ S ∈ univ.filter (fun S => v ∈ S), weight S

namespace FracColoring

variable {G : SimpleGraph V}

/-- The total weight of a fractional coloring, i.e. the LP objective. -/
noncomputable def total (c : FracColoring G) : ℝ := ∑ S : Finset V, c.weight S




/-- The singleton fractional coloring: weight `1` on every one-element (independent)
set and `0` elsewhere.  This witnesses feasibility of the LP. -/
noncomputable def singleton (G : SimpleGraph V) : FracColoring G where
  weight S := if S.card = 1 then 1 else 0
  nonneg S := by split <;> norm_num
  supp S hS := by
    split
    · rename_i h
      rw [Finset.card_eq_one] at h
      obtain ⟨a, rfl⟩ := h
      exact absurd (by simp [SimpleGraph.IsIndepSet]) hS
    · rfl
  covers v := by
    refine (Finset.single_le_sum (f := fun S : Finset V => if S.card = 1 then (1 : ℝ) else 0)
      (fun S _ => by dsimp only; split <;> norm_num) (a := {v}) (by simp)).trans_eq' ?_
    simp


end FracColoring


/-- The **geometric fractional chromatic number** of a finite graph: the infimum of the
total weight over all feasible fractional colorings. -/
noncomputable def geomFrac (G : SimpleGraph V) : ℝ :=
  sInf (Set.range (fun c : FracColoring G => c.total))








end GeomFrac

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  The Matolcsi–Ruzsa–Varga–Zsámboki bound
"`χ_f(plane) > 4`" is not really a plane statement: it is a *finite* statement about
one unit-distance graph with independence ratio below `1/4`.  Conjecture: the entire
plane-to-graph reduction is captured by the single inequality
`geomFrac G ≥ |V| / α(G)`, so that `4·α(G) < |V|` alone forces `geomFrac G > 4`.

**Experiment (Experimenter).**  We modelled the covering LP by `FracColoring` and
proved the weak-duality inequality `|V| ≤ α(G)·total(c)` by double counting
vertex–set incidences (`double_count`, `card_le_indepNum_mul_total`).  Taking the
infimum over feasible points gave `geomFrac_ge_ratio`, and the strict corollary
`geomFrac_gt_four_of_indep_ratio` followed by real arithmetic.

**Analysis (Analyst).**  The proof needs only: (i) independent sets have size `≤ α`;
(ii) the covering constraints; (iii) nonnegativity.  No geometry enters the engine —
geometry only supplies a graph `G` with `4·α(G) < |V|`.  The singleton coloring shows
feasibility and gives `geomFrac ≤ |V|`, so the LP value is finite and the infimum is
well posed.

**Critique (Critic).**  Is the statement vacuous?  No: `geomFrac_le_card` shows the
feasible set is nonempty and the value is a real infimum, and
`geomFrac_gt_four_of_indep_ratio` is discharged by genuine arithmetic (`linarith`,
`div_le_iff₀`), not `decide`.  The hypothesis `4·α(G) < |V|` is exactly the MRVZ
independence-ratio condition and is not always satisfiable (it fails for bipartite
graphs, where `α ≥ |V|/2`), so the theorem is not trivially true.

**Synthesis (PI).**  The engine is domain-free and reusable.  The geometric payload —
building `G` with small independence ratio from unit distances — is isolated in
`UnitDistanceFractional.lean`.
-/


