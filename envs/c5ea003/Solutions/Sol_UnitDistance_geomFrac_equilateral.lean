-- Prove2me | solution 1 for UnitDistance.geomFrac_equilateral
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:36:19.63312+00:00
-- url     : https://prove2.me/submissions/4cfa60d9-e692-4648-861f-be49e066531c

-- Sol generated from Geometry/UnitDistanceFractional.lean
import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
import Definitions.Def_Geometry_UnitDistanceFractional
import Theorems.Thm_GeomFrac_geomFrac_ge_ratio
import Theorems.Thm_GeomFrac_geomFrac_le_card
import Theorems.Thm_GeomFrac_indepNum_pos
/-
Copyright (c) 2026. All rights reserved.

# Unit-distance graphs and the fractional-chromatic engine

This file supplies the *geometric payload* for the independence-ratio engine of
`GeomFractionalChromatic.lean`, in the spirit of Matolcsi–Ruzsa–Varga–Zsámboki
(`MRVZ`), de Grey (`deGrey`) and Erdős (`Er87`).

We define the **unit-distance graph** on a finite family of points of the
Euclidean plane, characterise its independent sets geometrically, and connect it
to the LP lower bound `geomFrac G ≥ |V| / α(G)`.

## Main results

* `unitDistanceGraph` — the unit-distance graph of `p : V → ℝ²`.
* `unitDistanceGraph_adj_iff` / `isIndepSet_iff_no_unit` — the geometric reading:
  an independent set is a set of points with **no two at distance exactly `1`**.
* `equilateral` — a concrete equilateral triangle whose three vertices are
  pairwise at distance `1`; its unit-distance graph is complete, so its geometric
  fractional chromatic number is exactly `3` (`geomFrac_equilateral`).  This is the
  small-scale analogue of the `MRVZ` graph `G_27`, whose value is exactly `4`.
* `geomFrac_top_fin5_gt_four` — a concrete graph reaching the strict regime
  `geomFrac > 4`, showing the engine's conclusion is attainable.
* `exists_geomFrac_gt_four_of_low_indep_ratio` — **the MRVZ reduction as a bridge
  theorem**: the existence of *any* finite graph with independence ratio `< 1/4`
  yields a graph with geometric fractional chromatic number `> 4`.  Combined with a
  unit-distance realisation, this is precisely the statement that the fractional
  chromatic number of the plane exceeds `4`.
-/

open SimpleGraph Finset GeomFrac
open scoped BigOperators

open UnitDistance



@[simp] lemma unitDistanceGraph_adj_iff {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2))
    (u v : V) : (unitDistanceGraph p).Adj u v ↔ u ≠ v ∧ dist (p u) (p v) = 1 := Iff.rfl


/-! ### A concrete equilateral triangle -/


lemma dist_pt_horizontal : dist (pt 0 0) (pt 1 0) = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp [pt, Fin.sum_univ_two, Real.dist_eq]

lemma dist_pt_diag0 : dist (pt 0 0) (pt (1 / 2) (Real.sqrt 3 / 2)) = 1 := by
  rw [EuclideanSpace.dist_eq]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsum : (∑ i : Fin 2, dist ((pt 0 0).ofLp i)
      ((pt (1 / 2) (Real.sqrt 3 / 2)).ofLp i) ^ 2) = 1 := by
    simp [pt, Fin.sum_univ_two, Real.dist_eq]
    nlinarith [h3]
  rw [hsum, Real.sqrt_one]

lemma dist_pt_diag1 : dist (pt 1 0) (pt (1 / 2) (Real.sqrt 3 / 2)) = 1 := by
  rw [EuclideanSpace.dist_eq]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsum : (∑ i : Fin 2, dist ((pt 1 0).ofLp i)
      ((pt (1 / 2) (Real.sqrt 3 / 2)).ofLp i) ^ 2) = 1 := by
    simp [pt, Fin.sum_univ_two, Real.dist_eq]
    nlinarith [h3]
  rw [hsum, Real.sqrt_one]

/-- The equilateral triangle's unit-distance graph is complete: any two distinct
vertices are adjacent. -/
lemma equilateral_adj_iff (u v : Fin 3) :
    (unitDistanceGraph equilateral).Adj u v ↔ u ≠ v := by
  rw [unitDistanceGraph_adj_iff]
  refine ⟨fun h => h.1, fun huv => ⟨huv, ?_⟩⟩
  have h01 : dist (equilateral 0) (equilateral 1) = 1 := dist_pt_horizontal
  have h02 : dist (equilateral 0) (equilateral 2) = 1 := dist_pt_diag0
  have h12 : dist (equilateral 1) (equilateral 2) = 1 := dist_pt_diag1
  fin_cases u <;> fin_cases v <;> simp_all <;>
    first
      | exact h01 | exact h02 | exact h12
      | (rw [_root_.dist_comm]; first | exact h01 | exact h02 | exact h12)

/-- The equilateral triangle graph has independence number at most `1`
(it is a clique). -/
lemma equilateral_indepNum_le : (unitDistanceGraph equilateral).indepNum ≤ 1 := by
  obtain ⟨s, hind, hcard⟩ := (unitDistanceGraph equilateral).exists_isNIndepSet_indepNum
  rw [← hcard]
  by_contra hlt
  push_neg at hlt
  rw [Finset.one_lt_card] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := hlt
  exact (hind ha hb hab) ((equilateral_adj_iff a b).2 hab)


/-! ### The strict `> 4` regime -/





/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  Two bold claims: (1) the unit equilateral triangle
already realises the *tightness* phenomenon of the `MRVZ` engine — its geometric
fractional chromatic number should be exactly `3`, mirroring `G_27`'s exact `4`;
(2) the entire "plane `> 4`" reduction is a one-line consequence of the engine once a
graph with independence ratio `< 1/4` is in hand.

**Experiment (Experimenter).**  We built `unitDistanceGraph`, computed the three
equilateral distances in `EuclideanSpace ℝ (Fin 2)` via `EuclideanSpace.dist_eq` and
`Real.sq_sqrt` (the `√3/2` height reduces to `nlinarith`), and proved the triangle is
complete (`equilateral_adj_iff`, by `fin_cases`).  Hence `α = 1`, `|V| = 3`, and the
engine pins `geomFrac = 3` between the singleton upper bound and the ratio lower bound.
The strict `> 4` regime is realised concretely by `K₅` and abstractly by the bridge
theorem.

**Analysis (Analyst).**  Equilateral triangle: `geomFrac = |V|/α = 3`, exact because
`K_n` is vertex-transitive.  The obstruction to a *unit-distance* `> 4` example is
real: planar unit-distance graphs have large independent sets, so `4·α < |V|` fails
for every small unit-distance graph — this is exactly why `MRVZ` need `27`+`2`
vertices and a computer search.  `K₅` shows the engine's target value is attainable in
the abstract, isolating the difficulty as purely geometric (finding a *plane*
realisation with small independence ratio).

**Critique (Critic).**  No theorem is vacuous: `geomFrac_equilateral` computes an exact
real number via `le_antisymm`; `geomFrac_top_fin5_gt_four` uses the engine plus a real
strict inequality; the bridge theorem is a clean existential reduction, not a tautology
(its hypothesis fails for bipartite graphs).  The distance computations are honest
Euclidean-norm facts, not `decide`.  What we have **not** done — and honestly cannot at
this scale — is exhibit the `29`-vertex *unit-distance* witness itself; that requires
explicit coordinates and a large independence-number computation, recorded as a bold
future direction.

**Synthesis (PI).**  The geometry (distance computations, independence characterisation)
plugs directly into the domain-free engine.  The remaining gap is exactly the
`MRVZ` construction of a plane realisation with independence ratio `< 1/4`.
-/
open UnitDistance in
theorem solution: geomFrac (unitDistanceGraph equilateral) = 3 := by
  have hcard : Fintype.card (Fin 3) = 3 := by simp
  have hα1 : (unitDistanceGraph equilateral).indepNum ≤ 1 := equilateral_indepNum_le
  have hαpos : 0 < (unitDistanceGraph equilateral).indepNum := indepNum_pos _
  have hαeq : (unitDistanceGraph equilateral).indepNum = 1 := by omega
  refine le_antisymm ?_ ?_
  · -- upper bound: singleton coloring gives ≤ |V| = 3
    have := geomFrac_le_card (unitDistanceGraph equilateral)
    rwa [hcard] at this
  · -- lower bound: |V| / α = 3 / 1 = 3
    have hge := geomFrac_ge_ratio (unitDistanceGraph equilateral) hαpos
    rw [hcard, hαeq] at hge
    simpa using hge
