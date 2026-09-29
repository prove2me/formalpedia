-- Prove2me | solution 1 for KeplerMission.packing_foundations
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-28T00:20:01.680855+00:00
-- url     : https://prove2.me/submissions/63b29c8b-40d1-472a-b338-d33fc705f234

import Definitions.Def_Kepler_PackingModel
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Zorn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open KeplerMission

-- KIUMVTC: separation gives a closed discrete set, hence finitely many centers in a ball.
-- Reuses the local argument in Theorems/Thm_Kepler_PackingFoundations.lean.
private lemma finite_centersInBall {V : Set Space} (hV : IsPacking V)
    (a : Space) (r : ℝ) : (centersInBall V a r).Finite := by
  have hdiscrete : IsDiscrete V := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro v hv
    refine ⟨Metric.ball v 2, Metric.isOpen_ball, ?_⟩
    ext x
    constructor
    · intro hx
      have he : x = v := by
        by_contra hne
        exact (not_lt_of_ge (hV hx.2 hv hne)) (Metric.mem_ball.mp hx.1)
      exact Set.mem_singleton_iff.mpr he
    · rintro rfl
      exact ⟨Metric.mem_ball_self (by norm_num), hv⟩
  have hclosed : IsClosed V :=
    Metric.isClosed_of_pairwise_le_dist (by norm_num : (0 : ℝ) < 2) hV
  simpa only [centersInBall, Set.inter_comm] using
    Metric.finite_isBounded_inter_isClosed hdiscrete
      (Metric.isBounded_ball (x := a) (r := r)) hclosed

-- CPNKNXN: a maximal packing containing V is saturated.
private lemma exists_saturated_extension (V : Set Space) (hV : IsPacking V) :
    ∃ W : Set Space, V ⊆ W ∧ IsPacking W ∧ IsSaturated W := by
  obtain ⟨W, hVW, hW⟩ := zorn_subset_nonempty {W : Set Space | IsPacking W}
    (fun c hc hchain _ ↦
      ⟨⋃₀ c, hchain.pairwise_sUnion.mpr (fun s hs ↦ hc hs),
        fun s hs ↦ Set.subset_sUnion_of_mem hs⟩) V hV
  refine ⟨W, hVW, hW.prop, ?_⟩
  intro x
  by_contra hnot
  have hfar : ∀ v ∈ W, 2 ≤ dist x v := by
    intro v hv
    exact le_of_not_gt (fun hlt ↦ hnot ⟨v, hv, hlt⟩)
  have hinsert : IsPacking (insert x W) := by
    apply Set.Pairwise.insert hW.prop
    intro v hv _
    exact ⟨hfar v hv, by simpa only [dist_comm] using hfar v hv⟩
  have hx : x ∈ W := hW.2 hinsert (Set.subset_insert x W) (Set.mem_insert x W)
  have hxx := hfar x hx
  norm_num at hxx

theorem solution : KeplerMission.PackingFoundationContract := by
  intro V hV
  obtain ⟨W, hVW, hW, hsat⟩ := exists_saturated_extension V hV
  refine ⟨W, hVW, hW, hsat, ?_⟩
  intro a r
  have hfinite := finite_centersInBall hW a r
  exact ⟨finite_centersInBall hV a r, hfinite,
    Set.ncard_le_ncard (Set.inter_subset_inter_left _ hVW) hfinite⟩
