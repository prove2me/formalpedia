-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_nonglobal_edge_direction
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T16:26:05.026672+00:00
-- url     : https://prove2.me/submissions/234be796-dafa-428e-9584-304c82e33461

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem partial_monitoring_nonglobal_edge_direction
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hn_global : ¬ ∃ f : Fin k × 𝕊 → ℝ, IsGlobalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 := by
  classical
  let V := EuclideanSpace ℝ (Fin d)
  let T : (Fin k × 𝕊 → ℝ) →ₗ[ℝ] V :=
    { toFun := fun f ↦ WithLp.toLp 2 (fun i ↦ ∑ c : Fin k, f (c, G.Φ c i))
      map_add' := by
        intro f g
        apply WithLp.ofLp_injective
        funext i
        change (∑ c : Fin k, (f + g) (c, G.Φ c i)) =
          (∑ c : Fin k, f (c, G.Φ c i)) + ∑ c : Fin k, g (c, G.Φ c i)
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        apply WithLp.ofLp_injective
        funext i
        change (∑ c : Fin k, (r • f) (c, G.Φ c i)) =
          r * ∑ c : Fin k, f (c, G.Φ c i)
        simp [Finset.mul_sum] }
  let v : V := WithLp.toLp 2 (fun i ↦ G.L a i - G.L b i)
  have hv_not : v ∉ LinearMap.range T := by
    intro hv
    obtain ⟨f, hf⟩ := hv
    apply hn_global
    refine ⟨f, ?_⟩
    intro i
    have hfi := congrArg (fun z : V ↦ z i) hf
    change (∑ c : Fin k, f (c, G.Φ c i)) = G.L a i - G.L b i at hfi
    exact hfi
  let U : Submodule ℝ V := LinearMap.range T
  obtain ⟨z, hzU, w, hwU, hvzw⟩ := U.exists_add_mem_mem_orthogonal v
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hv_not
    change v ∈ U
    rw [hvzw, hw, add_zero]
    exact hzU
  have hvw : inner ℝ v w = ‖w‖ ^ 2 := by
    rw [hvzw, inner_add_left]
    have hzw : inner ℝ z w = 0 :=
      (U.mem_orthogonal w).mp hwU z hzU
    rw [hzw, zero_add, real_inner_self_eq_norm_sq]
  have hvw_pos : 0 < inner ℝ v w := by
    rw [hvw]
    positivity
  let qE : V := (inner ℝ v w)⁻¹ • w
  let q : Fin d → ℝ := fun i ↦ qE i
  refine ⟨q, ?_, ?_, ?_⟩
  · let oneF : Fin k × 𝕊 → ℝ := fun p ↦ if p.1 = a then 1 else 0
    have hTone : T oneF = WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ)) := by
      apply WithLp.ofLp_injective
      funext i
      simp only [T, oneF, WithLp.ofLp_toLp]
      change (∑ c : Fin k, if c = a then 1 else 0) = 1
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hcne
        simp [hcne]
      · simp
    have honeU : WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ)) ∈ U := ⟨oneF, hTone⟩
    have how : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) w = 0 :=
      (U.mem_orthogonal w).mp hwU _ honeU
    have : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) qE = 0 := by
      simp [qE, inner_smul_right, how]
    simpa [q, PiLp.inner_apply, mul_comm] using this
  · have : inner ℝ v qE = 1 := by
      simp [qE, inner_smul_right, hvw_pos.ne']
    change (∑ i, qE i * (G.L a i - G.L b i)) = 1 at this
    simpa [q, mul_comm] using this
  · intro c σ
    let basisF : Fin k × 𝕊 → ℝ := fun p ↦ if p.1 = c ∧ p.2 = σ then 1 else 0
    have hTbU : T basisF ∈ U := ⟨basisF, rfl⟩
    have hbw : inner ℝ (T basisF) w = 0 :=
      (U.mem_orthogonal w).mp hwU _ hTbU
    have hbq : inner ℝ (T basisF) qE = 0 := by
      simp [qE, inner_smul_right, hbw]
    have hfiber : (fun i ↦ (T basisF) i) =
        fun i ↦ if G.Φ c i = σ then 1 else 0 := by
      funext i
      simp only [T, basisF, WithLp.ofLp_toLp]
      change (∑ x : Fin k, if x = c ∧ G.Φ x i = σ then 1 else 0) =
        if G.Φ c i = σ then 1 else 0
      by_cases hsig : G.Φ c i = σ
      · rw [Finset.sum_eq_single c]
        · simp [hsig]
        · intro x _ hxne
          simp [hxne]
        · simp
      · rw [if_neg hsig]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : x = c
        · simp [hx, hsig]
        · simp [hx]
    rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) =
        ∑ i, (if G.Φ c i = σ then 1 else 0) * qE i by
          rw [Finset.sum_filter]
          simp [q]]
    change (∑ i, qE i * (T basisF) i) = 0 at hbq
    simp_rw [congrFun hfiber] at hbq
    simpa [mul_comm] using hbq

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hn_global : ¬ ∃ f : Fin k × 𝕊 → ℝ,
      BanditAlgorithm.IsGlobalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 :=
  BanditAlgorithm.partial_monitoring_nonglobal_edge_direction G a b hn_global
