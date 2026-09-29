-- Prove2me | Theorems.Thm_BoltzmannBridge_Filtration_stability_supDist
-- name    : BoltzmannBridge.Filtration.stability_supDist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:48.573031+00:00
-- url     : https://prove2.me/theorems/2cc7ad9c-67ba-4c08-90bd-d4f602f4f420
-- title:
--   CESH stability (interleaving form).
-- statement:
--   **CESH stability (interleaving form).**  Two filtrations whose weights are
--   uniformly within `D` are `D`-interleaved.
--
--   ```lean
--   theorem BoltzmannBridge.Filtration.stability_supDist(F G : Filtration α) {D : ℝ}
--       (hD : 0 ≤ D) (h : WeightCloseBy F G D) : Interleaved F G D := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BoltzmannBridge/BottleneckStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BoltzmannBridge/BottleneckStability.lean#L146

-- Thm stub generated from Applications/BoltzmannBridge/BottleneckStability.lean
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

theorem BoltzmannBridge.Filtration.stability_supDist(F G : Filtration α) {D : ℝ}
    (hD : 0 ≤ D) (h : WeightCloseBy F G D) : Interleaved F G D := by sorry
