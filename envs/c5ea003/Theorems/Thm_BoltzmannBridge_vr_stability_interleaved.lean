-- Prove2me | Theorems.Thm_BoltzmannBridge_vr_stability_interleaved
-- name    : BoltzmannBridge.vr_stability_interleaved
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:25:57.2901+00:00
-- url     : https://prove2.me/theorems/c695862d-ebbe-4d40-b9c8-6ed9b5f5bdb7
-- title:
--   Vietoris–Rips stability (interleaving form).
-- statement:
--   **Vietoris–Rips stability (interleaving form).**  If two distance matrices are
--   uniformly within `ε`, their VR filtrations are `ε`-interleaved.
--
--   ```lean
--   theorem BoltzmannBridge.vr_stability_interleaved(d₁ d₂ : α → α → ℝ) {ε : ℝ}
--       (hε : 0 ≤ ε) (h : ∀ x y, |d₁ x y - d₂ x y| ≤ ε) :
--       Filtration.Interleaved (diamFiltrationOf d₁) (diamFiltrationOf d₂) ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BoltzmannBridge/BottleneckStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BoltzmannBridge/BottleneckStability.lean#L229

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

theorem BoltzmannBridge.vr_stability_interleaved(d₁ d₂ : α → α → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x y, |d₁ x y - d₂ x y| ≤ ε) :
    Filtration.Interleaved (diamFiltrationOf d₁) (diamFiltrationOf d₂) ε := by sorry
