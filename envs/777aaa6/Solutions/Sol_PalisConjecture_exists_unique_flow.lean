-- Prove2me | solution 1 for PalisConjecture.exists_unique_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:52:44.496153+00:00
-- url     : https://prove2.me/submissions/d9a46abc-c344-4368-b007-cd28d54ce340

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff Topology
open Set Metric

namespace PalisFlowAux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x} {x₀ : M}

/-- Local existence of integral curves with a uniform existence time on a neighbourhood. -/
theorem exists_nhds_uniform
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧
      IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  have hF := (hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hα1, hαc⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  set y₀ := extChartAt I x₀ x₀ with hy₀
  have hmem : (y₀, (0 : ℝ)) ∈ closedBall y₀ (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε) :=
    ⟨mem_closedBall_self (by exact_mod_cast hr.le), by constructor <;> linarith⟩
  have hα0 : α (y₀, 0) = y₀ := (hα1 y₀ (mem_closedBall_self (by exact_mod_cast hr.le))).1
  have hT : interior (extChartAt I x₀).target ∈ 𝓝 (α (y₀, 0)) := by
    rw [hα0]; exact isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx)
  have hpre := hαc _ hmem hT
  rw [Filter.mem_map, mem_nhdsWithin] at hpre
  obtain ⟨u, hu, hyu, hsub⟩ := hpre
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu _ hyu
  set ρ := min δ (r : ℝ) with hρ
  have hρpos : 0 < ρ := lt_min hδ (by exact_mod_cast hr)
  set ε' := min δ ε with hε'
  have hε'pos : 0 < ε' := lt_min hδ hε
  refine ⟨(extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball y₀ ρ,
    Filter.inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds _ hρpos)),
    ε', hε'pos, ?_⟩
  rintro y ⟨hys, hyb⟩
  set z := extChartAt I x₀ y with hz
  have hzr : z ∈ closedBall y₀ (r : ℝ) :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hyb)
  have hzδ : z ∈ ball y₀ δ := ball_subset_ball (min_le_left _ _) hyb
  obtain ⟨hz0, hzd⟩ := hα1 z hzr
  set f : ℝ → E := fun t ↦ α (z, t) with hf
  refine ⟨(extChartAt I x₀).symm ∘ f, ?_, ?_⟩
  · have hz0' : α (z, 0) = z := hz0
    change (extChartAt I x₀).symm (α (z, 0)) = y
    rw [hz0', hz]
    exact (extChartAt I x₀).left_inv hys
  intro t ht
  have htε : t ∈ Ioo (0 - ε) (0 + ε) := by
    constructor
    · have := ht.1; have := min_le_right δ ε; linarith
    · have := ht.2; have := min_le_right δ ε; linarith
  have htδ : t ∈ ball (0 : ℝ) δ := by
    rw [Real.ball_eq_Ioo]
    constructor
    · have := ht.1; have := min_le_left δ ε; linarith
    · have := ht.2; have := min_le_left δ ε; linarith
  have hf3 : f t ∈ interior (extChartAt I x₀).target := by
    apply hsub
    refine ⟨hball ?_, hzr, Ioo_subset_Icc_self htε⟩
    rw [← ball_prod_same]
    exact ⟨hzδ, htδ⟩
  have h := (hzd t (Ioo_subset_Icc_self htε)).hasDerivAt (Icc_mem_nhds htε.1 htε.2)
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (f t)
  change HasDerivAt f (fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ)) t at h
  rw [← tangentCoordChange_def] at h
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  let w : E := v xₜ
  have h' : HasDerivAt f (tangentCoordChange I xₜ x₀ xₜ w) t := h
  have hcomp : tangentCoordChange I x₀ xₜ xₜ (tangentCoordChange I xₜ x₀ xₜ w) = w := by
    rw [tangentCoordChange_comp (w := xₜ) (x := x₀) (y := xₜ) (z := xₜ) ⟨⟨hft2, hft1⟩, hft2⟩,
      tangentCoordChange_self hft2]
  have hD : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f)
      (tangentCoordChange I x₀ xₜ xₜ (tangentCoordChange I xₜ x₀ xₜ w)) t := by
    apply HasFDerivAt.comp_hasDerivAt _ _ h'
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hf3⟩
    rw [← (extChartAt I x₀).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  rw [hcomp] at hD
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt, ?_⟩
  simp only [mfld_simps]
  exact hD.hasFDerivAt.hasFDerivWithinAt

end PalisFlowAux

open PalisConjecture in
theorem solution (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : IsCrVectorField r X) :
    ∃! Φ : ℝ → M → M, IsFlowOf X Φ := by
  have hv : ContMDiff (𝓡 n) (𝓡 n).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle (𝓡 n) M)) :=
    hX.of_le (by
      first
        | exact Nat.one_le_cast.mpr hr
        | (have h1 := Nat.mono_cast (α := WithTop ℕ∞) hr; rwa [Nat.cast_one] at h1)
        | exact_mod_cast hr
        | exact WithTop.coe_le_coe.mpr (by exact_mod_cast hr))
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨fun _ p ↦ p, fun p ↦ isEmptyElim p, fun Ψ _ ↦ ?_⟩
    funext t p
    exact isEmptyElim p
  have hloc := fun x : M ↦ PalisFlowAux.exists_nhds_uniform (hv x)
  choose U hU ε hε hcurve using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ ↦ hU x)
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := hM
    have := hs.2 (mem_univ x)
    simp only [mem_iUnion] at this
    obtain ⟨i, hi, _⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨x₁, hx₁, hmin⟩ := s.exists_min_image ε hsne
  have hunif : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (Ioo (-ε x₁) (ε x₁)) := by
    intro x
    have := hs.2 (mem_univ x)
    simp only [mem_iUnion] at this
    obtain ⟨i, hi, hxi⟩ := this
    obtain ⟨γ, hγ0, hγ⟩ := hcurve i x hxi
    refine ⟨γ, hγ0, hγ.mono ?_⟩
    have := hmin i hi
    exact Ioo_subset_Ioo (neg_le_neg this) this
  have hglob := fun x : M ↦ exists_isMIntegralCurve_of_isMIntegralCurveOn hv (hε x₁) hunif x
  choose γ hγ0 hγ using hglob
  refine ⟨fun t p ↦ γ p t, fun p ↦ ⟨hγ0 p, hγ p⟩, fun Ψ hΨ ↦ ?_⟩
  funext t p
  have := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv (hΨ p).2 (hγ p)
    (t₀ := 0) (by rw [(hΨ p).1, hγ0 p])
  exact congrFun this t
