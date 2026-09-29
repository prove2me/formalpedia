-- Prove2me | Theorems.Thm_RipsGuard_mem_ripsBall_iff_isRipsSimplex
-- name    : RipsGuard.mem_ripsBall_iff_isRipsSimplex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:09:35.570812+00:00
-- url     : https://prove2.me/theorems/8bf27da6-6bd2-47a5-a616-26ca21a0e16e
-- title:
--   The Rips ball is exactly the set of vertices spanning an edge with `v`: the link
-- statement:
--   The Rips ball is exactly the set of vertices spanning an edge with `v`: the link
--       degree is an invariant of the Rips complex, not just of the metric.
--
--   ```lean
--   theorem RipsGuard.mem_ripsBall_iff_isRipsSimplex[DecidableEq α] {S : Finset α} {ε : ℝ} {v x : α}
--       (hε : 0 ≤ ε) (hv : v ∈ S) :
--       x ∈ ripsBall S ε v ↔ IsRipsSimplex S ε ({v, x} : Finset α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/RipsLinkGuardedInterval.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/RipsLinkGuardedInterval.lean#L83

-- Thm stub generated from Bridges/GraphTheory/RipsLinkGuardedInterval.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_RipsLinkGuardedInterval
/-
  # Vertex Links of Rips Complexes and Stability of the Guarded Interval

  This file continues the Phase A thread on quantitative sphere detection from finite
  data.  The previous file
  (`Catalog/Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean`) established the
  *global* correspondence interleaving: a correspondence of distortion `≤ c` translates
  Rips scales by `c`, and the matched / Hausdorff cases give the sharp `2δ` translation.

  Directions 4 and 5 of the mission ask for the *local* counterpart: link data of the
  Rips complex, and an interval-valued detector whose endpoints are Lipschitz stable
  under matched perturbations of the sample.  This file develops exactly that, again as
  a chain in which each result uses the previous ones.

  ## The chain

  1. `IsRipsSimplex`, `ripsBall`, `linkDeg` — the closed vertex star of a sample point
     and its cardinality (the *link degree*); `mem_ripsBall_iff_isRipsSimplex` identifies
     the ball with the set of vertices spanning an edge with `v`, so the link degree is a
     genuine invariant of the Rips complex.
  2. `ripsBall_mono`, `linkDeg_mono` — link degrees are monotone in the scale.
  3. `IsDeltaMatching`, `dist_map_le` — a `δ`-matching expands distances by at most `2δ`
     (the local shadow of the `2δ` distortion bound of the previous file).
  4. `Separated`, `map_injOn` — on an `η`-separated sample with `2δ < η` a `δ`-matching is
     injective, so it cannot collapse links.
  5. `ripsBall_image_subset`, `linkDeg_le_of_matching` — hence link degrees can only grow:
     `linkDeg S ε v ≤ linkDeg T (ε + 2δ) (f v)`.
  6. `GuardedAt`, `GuardedAt_mono`, `GuardedAt_perturb` — the local guard "every link has
     at least `k` vertices" is an up-set in the scale and is transported by a `δ`-matching
     with a `2δ` shift.
  7. `exists_diam_bound`, `guardedAt_diam` — the guard is eventually satisfied, so the
     *guarded interval* `guardSet S k` is a nonempty up-set bounded below by `0`.
  8. `guardThreshold_stability` — **the endpoint of the guarded interval is `2δ`-Lipschitz
     under matched perturbations**: `guardThreshold T k ≤ guardThreshold S k + 2δ`, and
     symmetrically, giving the two-sided bound `guardThreshold_stability_abs`.
  9. `GuardedAt_perturb_ray` — the perturbed sample is guarded on the whole ray
     `[ε + 2δ, ∞)`: once acquired, the guard is never lost.
  10. `guardSet_pair`, `guardThreshold_pair` — a worked example: the guarded interval of
     the two-point sample `{0, r} ⊆ ℝ` with `k = 2` is exactly `[r, ∞)`, so the guard is
     not vacuous and the endpoint is computed exactly.
  11. `linkDeg_shift_sharp` — the shift `2δ` in step 5 cannot be lowered.

  The file is self-contained: it only imports Mathlib.
-/

open Finset

noncomputable section

open RipsGuard

variable {α : Type*} [PseudoMetricSpace α]

/-! ## Part 1: Rips simplices, balls and link degrees -/

theorem RipsGuard.mem_ripsBall_iff_isRipsSimplex[DecidableEq α] {S : Finset α} {ε : ℝ} {v x : α}
    (hε : 0 ≤ ε) (hv : v ∈ S) :
    x ∈ ripsBall S ε v ↔ IsRipsSimplex S ε ({v, x} : Finset α) := by sorry
