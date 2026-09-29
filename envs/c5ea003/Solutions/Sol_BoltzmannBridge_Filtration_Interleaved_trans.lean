-- Prove2me | solution 1 for BoltzmannBridge.Filtration.Interleaved_trans
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:48:55.02493+00:00
-- url     : https://prove2.me/submissions/c04817a8-5fd7-4126-9e46-a834b9f92455

-- Sol generated from Applications/BoltzmannBridge/BottleneckStability.lean
import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_BottleneckStability
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
/-
# The Boltzmann Bridge IV — The Interleaving Distance and Bottleneck Stability

This file closes the catalog's persistent-homology arc.  The earlier files built
the *filtration calculus* (`Applications.BoltzmannBridge.HigherPersistence`:
`Filtration`, `sublevelFaces`, `sublevel_mono`, the Vietoris–Rips `diamWeight`)
and the *relational interleaving lemmas*
(`Applications.BoltzmannBridge.PersistenceStability`: `stability_interleaving`,
`stability_compose`, `stability_two_sided`).  Those files produced a family of
scattered set-inclusion inequalities.  This file turns them into a single
coherent **metric theory of persistence stability**:

* a named, symmetric, additively-composable interleaving relation
  `Interleaved F G δ` (with `Interleaved_refl/symm/mono/trans`) — the relational
  skeleton of a graded preorder;
* a real-valued `interleavingDist`, shown to be a *symmetric, grounded
  pre-distance* (`interleavingDist_nonneg`, `interleavingDist_le`,
  `interleavingDist_self`, `interleavingDist_comm`);
* the Cohen-Steiner–Edelsbrunner–Harer sublevel stability theorem in sharp
  `1`-Lipschitz form: uniform `D`-closeness of the weights forces a
  `D`-interleaving and `interleavingDist ≤ D` (`stability_supDist`,
  `interleavingDist_le_supDist`);
* a Gromov–Hausdorff / correspondence-distortion layer over **explicit distance
  matrices** `d : α → α → ℝ` (`diamWeightOf`, `diamFiltrationOf`), resting on the
  single load-bearing estimate `diamWeightOf_dist_le` — *the simplex diameter is
  `1`-Lipschitz in the input metric* — yielding `vr_stability_interleaved` and
  `vr_stability_dist`;
* an end-to-end concrete certificate on two `3`-point clouds
  (`cloud_distortion`, `cloud_stability`, `cloud_interleavingDist_le`).

The entire stability phenomenon collapses onto one inequality: the simplex weight
is `1`-Lipschitz in the data.  Everything else is monotonicity bookkeeping.

## Main results

* `Interleaved_refl/symm/mono/trans` — interleaving is a graded preorder
* `interleavingDist_nonneg/le/self/comm` — a symmetric grounded pre-distance
* `stability_supDist`, `interleavingDist_le_supDist` — CESH `1`-Lipschitz stability
* `diamWeightOf_dist_le` — VR diameter is `1`-Lipschitz in the distance matrix
* `vr_stability_interleaved`, `vr_stability_dist` — distortion `≤ ε` ⇒ stability
* `cloud_distortion/stability/interleavingDist_le` — concrete point-cloud certificate
-/

open Finset BigOperators

open BoltzmannBridge

open Filtration

variable {α : Type*}

/-! ## The interleaving relation -/


-- !-- `0 ≤ 0`; and `F.sublevelFaces t ⊆ F.sublevelFaces (t+0)` simplifies via `t+0 = t`. -- !--

-- !-- Swap the two inclusion clauses; `0 ≤ δ` is preserved. -- !--

-- !-- Enlarge each shift via `sublevel_mono` (`t+δ ≤ t+δ'`); `0 ≤ δ ≤ δ'` by `linarith`. -- !--

-- !-- Chain the two interleavings' inclusions (cf. `stability_compose`); the shifts
-- !-- add since `t + (δ + δ') = (t + δ) + δ'`. -- !--

/-! ## The interleaving distance -/


-- !-- Every admissible shift is `≥ 0` (first component of `Interleaved`), so
-- !-- `Real.sInf_nonneg` gives the bound. -- !--

-- !-- `δ` lies in the shift set, which is bounded below by `0`; apply `csInf_le`. -- !--

-- !-- `≤ 0` from `interleavingDist_le` with `Interleaved_refl`, `≥ 0` from `nonneg`. -- !--

-- !-- `Interleaved_symm` makes the two shift sets equal, hence equal infima. -- !--

/-! ## Cohen-Steiner–Edelsbrunner–Harer sublevel stability (1-Lipschitz form) -/


-- !-- Each direction is `stability_two_sided`; the shift `D ≥ 0` packages the
-- !-- symmetric bound into an `Interleaved`. -- !--

-- !-- Combine `stability_supDist` with `interleavingDist_le`. -- !--


/-! ## Vietoris–Rips over explicit distance matrices -/


variable {α : Type*}


-- !-- `0` always sits in the inserted set, so the `sup'` dominates it via `le_sup'`. -- !--

-- !-- The empty product is empty, so the `sup'` is over `{0}`, giving `0`. -- !--

-- !-- Every pairwise distance of `σ` is a pairwise distance of `τ ⊇ σ`, so the
-- !-- smaller `sup'` is dominated by the larger one (`sup'_le` + `le_sup'`). -- !--


-- !-- The load-bearing `1`-Lipschitz estimate: bound each `d₁ x y ≤ d₂ x y + ε ≤`
-- !-- `diamWeightOf d₂ σ + ε`, and `0 ≤ diamWeightOf d₂ σ + ε`; then `sup'_le` both
-- !-- ways and `abs_sub_le_iff`. -- !--

-- !-- Apply `diamWeightOf_dist_le` to every `σ` to get `WeightCloseBy`, then
-- !-- `stability_supDist`. -- !--

-- !-- `interleavingDist_le` applied to `vr_stability_interleaved`. -- !--


/-! ## A concrete point-cloud certificate -/




-- !-- A finite `Fin 3 × Fin 3` case split; each entry differs by `0` or `1/10`. -- !--

-- !-- `vr_stability_interleaved` with the `cloud_distortion` bound. -- !--

-- !-- `vr_stability_dist` with the `cloud_distortion` bound. -- !--


/-
-- !-- Lab Notebook -- !--

## Hypothesis
The scattered set-inclusion stability inequalities of `PersistenceStability`
(`stability_interleaving`, `stability_compose`, `stability_two_sided`) are the
shadow of a single *metric* statement: there is a real-valued interleaving
distance on filtrations under which persistence is `1`-Lipschitz in the data, and
the whole Vietoris–Rips stability theory reduces to the diameter being
`1`-Lipschitz in the distance matrix.

## Result
Confirmed.  `Interleaved` is a graded preorder (`refl/symm/mono/trans`),
`interleavingDist` is a symmetric grounded pre-distance bounded above by any
witness, and `interleavingDist_le_supDist` is the sharp CESH `1`-Lipschitz bound.
Over explicit distance matrices the entire theory rests on the single estimate
`diamWeightOf_dist_le`; `vr_stability_dist` and the concrete `cloud_*` certificate
follow as monotonicity bookkeeping.

## Insight
`Interleaved_trans` *is* the triangle inequality, already at the relational level,
and `diamWeightOf_dist_le` (a one-line `sup'` Lipschitz estimate) *is* the entire
Gromov–Hausdorff–to–bottleneck pipeline.  Removing metric-space structure in
favour of a bare matrix `d : α → α → ℝ` makes the Lipschitz content transparent
and decouples VR stability from `PseudoMetricSpace`.

## Failure analysis
The honest fault line is `interleavingDist`: with `sInf ∅ = 0`, two
never-interleaved filtrations are reported at distance `0`, so the triangle
inequality for `interleavingDist` is *not* unconditionally true in `ℝ` — it needs
either a finiteness/witness hypothesis or an `EReal` codomain.  We therefore prove
only the unconditional facts (`nonneg`, `le`, `self`, `comm`) and document the
`EReal` upgrade as Future Direction 1.
-/


open BoltzmannBridge.Filtration in
theorem solution{F G H : Filtration α} {δ δ' : ℝ}
    (h₁ : Interleaved F G δ) (h₂ : Interleaved G H δ') :
    Interleaved F H (δ + δ') := by
  refine ⟨by linarith [h₁.1, h₂.1], fun t => ?_, fun t => ?_⟩
  · have := Set.Subset.trans (h₁.2.1 t) (h₂.2.1 (t + δ))
    rwa [add_assoc] at this
  · have := Set.Subset.trans (h₂.2.2 t) (h₁.2.2 (t + δ'))
    rwa [add_assoc, add_comm δ' δ] at this
