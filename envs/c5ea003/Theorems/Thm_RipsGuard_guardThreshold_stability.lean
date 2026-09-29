-- Prove2me | Theorems.Thm_RipsGuard_guardThreshold_stability
-- name    : RipsGuard.guardThreshold_stability
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:09:28.487231+00:00
-- url     : https://prove2.me/theorems/9bcbf36e-95f9-44e7-843e-d22ac098c486
-- title:
--   Endpoint stability (one-sided).
-- statement:
--   **Endpoint stability (one-sided).**  Under a `δ`-matching of an `η`-separated sample
--       with `2δ < η`, the endpoint of the guarded interval moves by at most `2δ`.
--
--   ```lean
--   theorem RipsGuard.guardThreshold_stability[DecidableEq α] {S T : Finset α} {f : α → α}
--       {δ η : ℝ} {k : ℕ} (hf : IsDeltaMatching S T f δ) (hsep : Separated S η)
--       (hη : 2 * δ < η) (hk : 1 ≤ k) (hkS : k ≤ S.card) :
--       guardThreshold T k ≤ guardThreshold S k + 2 * δ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/RipsLinkGuardedInterval.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/RipsLinkGuardedInterval.lean#L268

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








/-! ## Part 2: Monotonicity in the scale -/



/-! ## Part 3: `δ`-matchings and injectivity on separated samples -/






/-! ## Part 4: Link degrees are stable under matched perturbations -/



/-! ## Part 5: The local guard and its transport -/




/-! ## Part 6: The guarded interval and its endpoint -/

theorem RipsGuard.guardThreshold_stability[DecidableEq α] {S T : Finset α} {f : α → α}
    {δ η : ℝ} {k : ℕ} (hf : IsDeltaMatching S T f δ) (hsep : Separated S η)
    (hη : 2 * δ < η) (hk : 1 ≤ k) (hkS : k ≤ S.card) :
    guardThreshold T k ≤ guardThreshold S k + 2 * δ := by sorry
