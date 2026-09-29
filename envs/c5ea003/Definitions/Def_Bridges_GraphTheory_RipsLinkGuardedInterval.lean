-- Prove2me | Definitions.Def_Bridges_GraphTheory_RipsLinkGuardedInterval
-- name    : Bridges_GraphTheory_RipsLinkGuardedInterval
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:24.698113+00:00
-- url     : https://prove2.me/theorems/afa9d2cd-ec1a-48a9-a0d9-37aafa248cbb
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_RipsLinkGuardedInterval
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.RipsLinkGuardedInterval`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/RipsLinkGuardedInterval.lean by skeleton subtraction
import Mathlib
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

namespace RipsGuard

variable {α : Type*} [PseudoMetricSpace α]

/-! ## Part 1: Rips simplices, balls and link degrees -/

/-- `s` is a simplex of the Vietoris–Rips complex of the finite sample `S` at scale `ε`:
    a subset of `S` of diameter at most `ε`. -/
def IsRipsSimplex (S : Finset α) (ε : ℝ) (s : Finset α) : Prop :=
  s ⊆ S ∧ ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε


open Classical in
/-- The closed Rips ball (closed vertex star) of `v` in the sample `S` at scale `ε`. -/
def ripsBall (S : Finset α) (ε : ℝ) (v : α) : Finset α :=
  S.filter (fun x => dist v x ≤ ε)



/-- The link degree of `v`: the number of sample points joined to `v` at scale `ε`
    (including `v` itself when `0 ≤ ε`). -/
def linkDeg (S : Finset α) (ε : ℝ) (v : α) : ℕ := (ripsBall S ε v).card


/-! ## Part 2: Monotonicity in the scale -/



/-! ## Part 3: `δ`-matchings and injectivity on separated samples -/

/-- `f` is a `δ`-matching of the sample `S` onto the sample `T`: it moves every point of
    `S` by at most `δ` into `T`, and every point of `T` is hit. -/
def IsDeltaMatching (S T : Finset α) (f : α → α) (δ : ℝ) : Prop :=
  (∀ x ∈ S, f x ∈ T ∧ dist x (f x) ≤ δ) ∧ (∀ y ∈ T, ∃ x ∈ S, f x = y)



/-- `S` is `η`-separated: distinct sample points are at distance at least `η`. -/
def Separated (S : Finset α) (η : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → η ≤ dist x y


/-! ## Part 4: Link degrees are stable under matched perturbations -/



/-! ## Part 5: The local guard and its transport -/

/-- The sample `S` is *`k`-guarded at scale `ε`*: every vertex link contains at least `k`
    vertices.  This is the local manifold-like condition of Direction 4, in its simplest
    quantitative form. -/
def GuardedAt (S : Finset α) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ v ∈ S, k ≤ linkDeg S ε v



/-! ## Part 6: The guarded interval and its endpoint -/



/-- The set of scales at which the `k`-guard holds — the *guarded interval*. -/
def guardSet (S : Finset α) (k : ℕ) : Set ℝ := {ε : ℝ | GuardedAt S k ε}



/-- The left endpoint of the guarded interval: the smallest scale at which every link of
    the sample has at least `k` vertices. -/
def guardThreshold (S : Finset α) (k : ℕ) : ℝ := sInf (guardSet S k)




/-! ## Part 7: The guarded interval is a ray, and a worked example -/




/-! ## Part 8: Sharpness of the `2δ` shift for link degrees -/


end RipsGuard

end


