-- Prove2me | solution 1 for RipsGuard.guardThreshold_stability
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:41:14.13207+00:00
-- url     : https://prove2.me/submissions/1103eb87-a8e0-4a65-abeb-34f3bc820218

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


/-- A `δ`-matching expands distances by at most `2δ` — the local form of the `2δ`
    distortion bound for matched samples. -/
theorem dist_map_le {S T : Finset α} {f : α → α} {δ : ℝ}
    (hf : IsDeltaMatching S T f δ) {x x' : α} (hx : x ∈ S) (hx' : x' ∈ S) :
    dist (f x) (f x') ≤ dist x x' + 2 * δ := by
  have h1 : dist x (f x) ≤ δ := (hf.1 x hx).2
  have h2 : dist x' (f x') ≤ δ := (hf.1 x' hx').2
  calc dist (f x) (f x') ≤ dist (f x) x + dist x (f x') := dist_triangle _ _ _
    _ ≤ dist (f x) x + (dist x x' + dist x' (f x')) := by
        gcongr; exact dist_triangle _ _ _
    _ = dist x (f x) + dist x x' + dist x' (f x') := by rw [dist_comm (f x) x]; ring
    _ ≤ δ + dist x x' + δ := by gcongr
    _ = dist x x' + 2 * δ := by ring

/-- A `δ`-matching contracts distances by at most `2δ` as well. -/
theorem le_dist_map {S T : Finset α} {f : α → α} {δ : ℝ}
    (hf : IsDeltaMatching S T f δ) {x x' : α} (hx : x ∈ S) (hx' : x' ∈ S) :
    dist x x' ≤ dist (f x) (f x') + 2 * δ := by
  have h1 : dist x (f x) ≤ δ := (hf.1 x hx).2
  have h2 : dist x' (f x') ≤ δ := (hf.1 x' hx').2
  calc dist x x' ≤ dist x (f x) + dist (f x) x' := dist_triangle _ _ _
    _ ≤ dist x (f x) + (dist (f x) (f x') + dist (f x') x') := by
        gcongr; exact dist_triangle _ _ _
    _ = dist x (f x) + dist (f x) (f x') + dist x' (f x') := by
        rw [dist_comm (f x') x']; ring
    _ ≤ δ + dist (f x) (f x') + δ := by gcongr
    _ = dist (f x) (f x') + 2 * δ := by ring


/-- On an `η`-separated sample with `2δ < η`, a `δ`-matching is injective: it cannot
    collapse two sample points, hence cannot destroy link data. -/
theorem map_injOn {S T : Finset α} {f : α → α} {δ η : ℝ}
    (hf : IsDeltaMatching S T f δ) (hsep : Separated S η) (hη : 2 * δ < η) :
    Set.InjOn f S := by
  intro x hx x' hx' heq
  by_contra hne
  have hxS : x ∈ S := hx
  have hx'S : x' ∈ S := hx'
  have hsp : η ≤ dist x x' := hsep x hxS x' hx'S hne
  have hle : dist x x' ≤ dist (f x) (f x') + 2 * δ := le_dist_map hf hxS hx'S
  rw [heq, dist_self] at hle
  linarith

/-! ## Part 4: Link degrees are stable under matched perturbations -/

theorem ripsBall_image_subset [DecidableEq α] {S T : Finset α} {f : α → α}
    {δ ε : ℝ} (hf : IsDeltaMatching S T f δ) {v : α} (hv : v ∈ S) :
    (ripsBall S ε v).image f ⊆ ripsBall T (ε + 2 * δ) (f v) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hxS, hd⟩ := mem_ripsBall.mp hx
  refine mem_ripsBall.mpr ⟨(hf.1 x hxS).1, ?_⟩
  calc dist (f v) (f x) ≤ dist v x + 2 * δ := dist_map_le hf hv hxS
    _ ≤ ε + 2 * δ := by gcongr

/-- **Local stability.** For a `δ`-matching of an `η`-separated sample with `2δ < η`, the
    link degree at `v` is dominated by the link degree at `f v` after a `2δ` shift. -/
theorem linkDeg_le_of_matching [DecidableEq α] {S T : Finset α} {f : α → α}
    {δ η ε : ℝ} (hf : IsDeltaMatching S T f δ) (hsep : Separated S η) (hη : 2 * δ < η)
    {v : α} (hv : v ∈ S) :
    linkDeg S ε v ≤ linkDeg T (ε + 2 * δ) (f v) := by
  have hinj : Set.InjOn f (ripsBall S ε v : Set α) :=
    (map_injOn hf hsep hη).mono (Finset.coe_subset.mpr ripsBall_subset)
  calc linkDeg S ε v = ((ripsBall S ε v).image f).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ linkDeg T (ε + 2 * δ) (f v) :=
        Finset.card_le_card (ripsBall_image_subset hf hv)

/-! ## Part 5: The local guard and its transport -/



/-- **Transport of the guard.**  A `δ`-matching of an `η`-separated sample with `2δ < η`
    carries a `k`-guard at scale `ε` to a `k`-guard at scale `ε + 2δ`. -/
theorem GuardedAt_perturb [DecidableEq α] {S T : Finset α} {f : α → α}
    {δ η ε : ℝ} {k : ℕ} (hf : IsDeltaMatching S T f δ) (hsep : Separated S η)
    (hη : 2 * δ < η) (hG : GuardedAt S k ε) : GuardedAt T k (ε + 2 * δ) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hf.2 w hw
  exact (hG v hv).trans (linkDeg_le_of_matching hf hsep hη hv)

/-! ## Part 6: The guarded interval and its endpoint -/

/-- Every finite sample has a finite diameter bound. -/
theorem exists_diam_bound (S : Finset α) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D := by
  classical
  by_cases h : (S ×ˢ S).Nonempty
  · obtain ⟨p, _, hmax⟩ := Finset.exists_max_image (S ×ˢ S) (fun p => dist p.1 p.2) h
    exact ⟨dist p.1 p.2, dist_nonneg, fun x hx y hy => hmax (x, y) (Finset.mk_mem_product hx hy)⟩
  · exact ⟨0, le_refl 0, fun x hx y hy => absurd ⟨(x, y), Finset.mk_mem_product hx hy⟩ h⟩

/-- At a diameter scale the whole sample lies in every link, so the guard holds with
    `k = S.card`; in particular the guarded interval is nonempty for every `k ≤ S.card`. -/
theorem guardedAt_diam {S : Finset α} {D : ℝ} (hD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    GuardedAt S S.card D := by
  intro v hv
  refine Finset.card_le_card ?_
  intro x hx
  exact mem_ripsBall.mpr ⟨hx, hD v hv x hx⟩


theorem guardSet_nonempty {S : Finset α} {k : ℕ} (hk : k ≤ S.card) :
    (guardSet S k).Nonempty := by
  obtain ⟨D, _, hD⟩ := exists_diam_bound S
  exact ⟨D, fun v hv => hk.trans (guardedAt_diam hD v hv)⟩

theorem guardSet_bddBelow {S : Finset α} {k : ℕ} (hS : S.Nonempty) (hk : 1 ≤ k) :
    BddBelow (guardSet S k) := by
  obtain ⟨v, hv⟩ := hS
  refine ⟨0, fun ε hε => ?_⟩
  have hpos : 0 < linkDeg S ε v := lt_of_lt_of_le hk (hε v hv)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact le_trans dist_nonneg (mem_ripsBall.mp hx).2





/-! ## Part 7: The guarded interval is a ray, and a worked example -/




/-! ## Part 8: Sharpness of the `2δ` shift for link degrees -/




open RipsGuard in
theorem solution[DecidableEq α] {S T : Finset α} {f : α → α}
    {δ η : ℝ} {k : ℕ} (hf : IsDeltaMatching S T f δ) (hsep : Separated S η)
    (hη : 2 * δ < η) (hk : 1 ≤ k) (hkS : k ≤ S.card) :
    guardThreshold T k ≤ guardThreshold S k + 2 * δ := by
  have hScard : 0 < S.card := lt_of_lt_of_le hk hkS
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hScard
  have hT : T.Nonempty := ⟨f v, (hf.1 v hv).1⟩
  have hAne : (guardSet S k).Nonempty := guardSet_nonempty hkS
  have hBbdd : BddBelow (guardSet T k) := guardSet_bddBelow hT hk
  have key : ∀ ε ∈ guardSet S k, guardThreshold T k ≤ ε + 2 * δ := by
    intro ε hε
    exact csInf_le hBbdd (GuardedAt_perturb hf hsep hη hε)
  have h : guardThreshold T k - 2 * δ ≤ guardThreshold S k :=
    le_csInf hAne (fun ε hε => by linarith [key ε hε])
  linarith
