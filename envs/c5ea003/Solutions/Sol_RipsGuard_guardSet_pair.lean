-- Prove2me | solution 1 for RipsGuard.guardSet_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:41:04.791481+00:00
-- url     : https://prove2.me/submissions/8b57fcc4-060e-487c-881a-dbbf70c91d2c

-- Sol generated from Bridges/GraphTheory/RipsLinkGuardedInterval.lean
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




theorem mem_ripsBall {S : Finset α} {ε : ℝ} {v x : α} :
    x ∈ ripsBall S ε v ↔ x ∈ S ∧ dist v x ≤ ε := by
  classical
  simp [ripsBall, Finset.mem_filter]

theorem ripsBall_subset {S : Finset α} {ε : ℝ} {v : α} : ripsBall S ε v ⊆ S :=
  fun _ hx => (mem_ripsBall.mp hx).1



/-! ## Part 2: Monotonicity in the scale -/



/-! ## Part 3: `δ`-matchings and injectivity on separated samples -/






/-! ## Part 4: Link degrees are stable under matched perturbations -/



/-! ## Part 5: The local guard and its transport -/




/-! ## Part 6: The guarded interval and its endpoint -/










/-! ## Part 7: The guarded interval is a ray, and a worked example -/




/-! ## Part 8: Sharpness of the `2δ` shift for link degrees -/




open RipsGuard in
theorem solution{r : ℝ} (hr : 0 < r) :
    guardSet ({0, r} : Finset ℝ) 2 = Set.Ici r := by
  have hne : (0 : ℝ) ≠ r := ne_of_lt hr
  have hcard : ({0, r} : Finset ℝ).card = 2 := Finset.card_pair hne
  ext ε
  simp only [Set.mem_Ici, guardSet, Set.mem_setOf_eq]
  constructor
  · intro hG
    have h2 : 2 ≤ (ripsBall ({0, r} : Finset ℝ) ε 0).card := by
      have := hG 0 (by simp); simpa [linkDeg] using this
    have heq : ripsBall ({0, r} : Finset ℝ) ε 0 = {0, r} :=
      Finset.eq_of_subset_of_card_le ripsBall_subset (by rw [hcard]; exact h2)
    have hr' : r ∈ ripsBall ({0, r} : Finset ℝ) ε 0 := by rw [heq]; simp
    have := (mem_ripsBall.mp hr').2
    rwa [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hr] at this
  · intro hε v hv
    have hball : ripsBall ({0, r} : Finset ℝ) ε v = {0, r} := by
      refine Finset.Subset.antisymm ripsBall_subset ?_
      intro x hx
      refine mem_ripsBall.mpr ⟨hx, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hx
      rcases hv with hv | hv <;> rcases hx with hx | hx <;> rw [hv, hx] <;>
        simp only [Real.dist_eq, sub_self, sub_zero, zero_sub, abs_zero, abs_neg,
          abs_of_pos hr] <;> linarith
    rw [linkDeg, hball, hcard]
