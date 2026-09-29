-- Prove2me | Theorems.Thm_BoltzmannBridge_Filtration_Interleaved_trans
-- name    : BoltzmannBridge.Filtration.Interleaved_trans
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:58.838205+00:00
-- url     : https://prove2.me/theorems/aaa2646a-f0fb-438d-8a3d-91ff594eca71
-- title:
--   Additivity / triangle inequality at the relational level.
-- statement:
--   **Additivity / triangle inequality at the relational level.**  A
--   `δ`-interleaving composed with a `δ'`-interleaving is a `(δ + δ')`-interleaving.
--   This is the engine behind the triangle inequality for `interleavingDist`.
--
--   ```lean
--   theorem BoltzmannBridge.Filtration.Interleaved_trans{F G H : Filtration α} {δ δ' : ℝ}
--       (h₁ : Interleaved F G δ) (h₂ : Interleaved G H δ') :
--       Interleaved F H (δ + δ') := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BoltzmannBridge/BottleneckStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BoltzmannBridge/BottleneckStability.lean#L88

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

theorem BoltzmannBridge.Filtration.Interleaved_trans{F G H : Filtration α} {δ δ' : ℝ}
    (h₁ : Interleaved F G δ) (h₂ : Interleaved G H δ') :
    Interleaved F H (δ + δ') := by sorry
