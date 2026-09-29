-- Prove2me | solution 1 for RipsGuard.linkDeg_shift_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:41:14.611981+00:00
-- url     : https://prove2.me/submissions/e2a49e0d-55a3-454d-9158-4ea299a1b924

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
theorem solution{δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 ≤ η)
    (hlt : η < ε + 2 * δ) :
    ∃ (S T : Finset ℝ) (f : ℝ → ℝ),
      IsDeltaMatching S T f δ ∧ linkDeg S ε 0 = 2 ∧ linkDeg T η (f 0) = 1 := by
  classical
  set f : ℝ → ℝ := fun x => if x = 0 then -δ else ε + δ with hfdef
  have hf0 : f 0 = -δ := by simp [hfdef]
  have hfe : f ε = ε + δ := by simp [hfdef, ne_of_gt hε]
  have hne0 : (0 : ℝ) ≠ ε := ne_of_lt hε
  have hneT : (-δ : ℝ) ≠ ε + δ := by intro h; linarith
  refine ⟨{0, ε}, {-δ, ε + δ}, f, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `f` is a `δ`-matching
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [h, hf0]
      refine ⟨by simp, ?_⟩
      rw [Real.dist_eq]
      simp [abs_of_pos hδ]
    · rw [h, hfe]
      refine ⟨by simp, ?_⟩
      rw [Real.dist_eq, show ε - (ε + δ) = -δ by ring, abs_neg, abs_of_pos hδ]
  · -- every point of `T` is hit
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h
    · exact ⟨0, by simp, by rw [hf0, h]⟩
    · exact ⟨ε, by simp, by rw [hfe, h]⟩
  · -- the link of `0` in `S` at scale `ε` has two vertices
    have hball : ripsBall ({0, ε} : Finset ℝ) ε 0 = {0, ε} := by
      refine Finset.Subset.antisymm ripsBall_subset ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact mem_ripsBall.mpr ⟨by simp [h], by simp [h, hε.le]⟩
      · refine mem_ripsBall.mpr ⟨by simp [h], ?_⟩
        rw [h, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hε]
    rw [linkDeg, hball, Finset.card_pair hne0]
  · -- after the perturbation the link of `f 0` at any scale `η < ε + 2δ` has one vertex
    have hball : ripsBall ({-δ, ε + δ} : Finset ℝ) η (-δ) = {-δ} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro x hx
        obtain ⟨hxT, hd⟩ := mem_ripsBall.mp hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
        rcases hxT with h | h
        · simp [h]
        · exfalso
          rw [h, Real.dist_eq, show -δ - (ε + δ) = -(ε + 2 * δ) by ring, abs_neg,
            abs_of_pos (by linarith : (0 : ℝ) < ε + 2 * δ)] at hd
          linarith
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        refine mem_ripsBall.mpr ⟨by simp [hx], ?_⟩
        rw [hx, dist_self]
        exact hη
    rw [hf0, linkDeg, hball, Finset.card_singleton]
