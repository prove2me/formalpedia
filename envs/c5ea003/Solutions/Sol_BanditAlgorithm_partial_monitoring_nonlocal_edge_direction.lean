-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_nonlocal_edge_direction
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:20:28.424072+00:00
-- url     : https://prove2.me/submissions/395bdde3-1706-45df-98b8-acf9df438672

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 1,
printed pp.489--490, Eq. (37.6).  The feedback map below is the transpose of
the book's stacked signal matrix, with its domain indexed only by actions in
`N_ab`.
-/

theorem partial_monitoring_nonlocal_edge_direction
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hnlocal : ¬ ∃ f : Fin k × 𝕊 → ℝ, IsLocalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, c ∈ pmNeighbourhood G a b → ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 := by
  classical
  let N := {c : Fin k // c ∈ pmNeighbourhood G a b}
  let V := EuclideanSpace ℝ (Fin d)
  let T : (N × 𝕊 → ℝ) →ₗ[ℝ] V :=
    { toFun := fun f ↦ WithLp.toLp 2 (fun i ↦ ∑ c : N, f (c, G.Φ c.1 i))
      map_add' := by
        intro f g
        apply WithLp.ofLp_injective
        funext i
        change (∑ c : N, (f + g) (c, G.Φ c.1 i)) =
          (∑ c : N, f (c, G.Φ c.1 i)) + ∑ c : N, g (c, G.Φ c.1 i)
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        apply WithLp.ofLp_injective
        funext i
        change (∑ c : N, (r • f) (c, G.Φ c.1 i)) =
          r * ∑ c : N, f (c, G.Φ c.1 i)
        simp [Finset.mul_sum] }
  let v : V := WithLp.toLp 2 (fun i ↦ G.L a i - G.L b i)
  have hv_not : v ∉ LinearMap.range T := by
    intro hv
    obtain ⟨f, hf⟩ := hv
    let f' : Fin k × 𝕊 → ℝ := fun p ↦
      if hp : p.1 ∈ pmNeighbourhood G a b then f (⟨p.1, hp⟩, p.2) else 0
    apply hnlocal
    refine ⟨f', ?_, ?_⟩
    · intro i
      have hfi := congrArg (fun z : V ↦ z i) hf
      change (∑ c : N, f (c, G.Φ c.1 i)) = G.L a i - G.L b i at hfi
      rw [← hfi]
      simp only [f']
      let g : Fin k → ℝ := fun c ↦
        if hc : c ∈ pmNeighbourhood G a b then f (⟨c, hc⟩, G.Φ c i) else 0
      calc
        (∑ c : Fin k, if hc : c ∈ pmNeighbourhood G a b then
            f (⟨c, hc⟩, G.Φ c i) else 0) =
            ∑ c ∈ Finset.univ.filter (fun c : Fin k ↦
              c ∈ pmNeighbourhood G a b), g c := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro c _
                by_cases hc : c ∈ pmNeighbourhood G a b <;> simp [g, hc]
        _ = ∑ c : N, g c := by
          simpa using (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (Fin k))) g
            (p := fun c : Fin k ↦ c ∈ pmNeighbourhood G a b)).symm
        _ = ∑ c : N, f (c, G.Φ c.1 i) := by
          apply Finset.sum_congr rfl
          intro c _
          simp [g, c.2]
    · intro c hc σ
      simp [f', hc]
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
  · have haN : a ∈ pmNeighbourhood G a b := by
      intro u hu
      exact hu.1
    let oneF : N × 𝕊 → ℝ := fun p ↦ if p.1.1 = a then 1 else 0
    have hTone : T oneF = WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ)) := by
      apply WithLp.ofLp_injective
      funext i
      simp only [T, oneF, WithLp.ofLp_toLp]
      change (∑ c : N, if c.1 = a then 1 else 0) = 1
      rw [Finset.sum_eq_single ⟨a, haN⟩]
      · simp
      · intro c _ hcne
        have hcval : c.1 ≠ a := by
          intro h
          apply hcne
          exact Subtype.ext h
        simp [hcval]
      · simp
    have honeU : WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ)) ∈ U := by
      exact ⟨oneF, hTone⟩
    have how : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) w = 0 :=
      (U.mem_orthogonal w).mp hwU _ honeU
    have : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) qE = 0 := by
      simp [qE, inner_smul_right, how]
    simpa [q, PiLp.inner_apply, mul_comm] using this
  · have : inner ℝ v qE = 1 := by
      simp [qE, inner_smul_right, hvw_pos.ne']
    change (∑ i, qE i * (G.L a i - G.L b i)) = 1 at this
    simpa [q, mul_comm] using this
  · intro c hc σ
    let basisF : N × 𝕊 → ℝ := fun p ↦ if p.1.1 = c ∧ p.2 = σ then 1 else 0
    have hTbU : T basisF ∈ U := ⟨basisF, rfl⟩
    have hbw : inner ℝ (T basisF) w = 0 :=
      (U.mem_orthogonal w).mp hwU _ hTbU
    have hbq : inner ℝ (T basisF) qE = 0 := by
      simp [qE, inner_smul_right, hbw]
    have hfiber : (fun i ↦ (T basisF) i) =
        fun i ↦ if G.Φ c i = σ then 1 else 0 := by
      funext i
      simp only [T, basisF, WithLp.ofLp_toLp]
      change (∑ x : N, if x.1 = c ∧ G.Φ x.1 i = σ then 1 else 0) =
        if G.Φ c i = σ then 1 else 0
      by_cases hsig : G.Φ c i = σ
      · rw [Finset.sum_eq_single ⟨c, hc⟩]
        · simp [hsig]
        · intro x _ hxne
          have hxval : x.1 ≠ c := by
            intro h
            apply hxne
            exact Subtype.ext h
          simp [hxval]
        · simp
      · rw [if_neg hsig]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hxval : x.1 = c
        · simp [hxval, hsig]
        · simp [hxval]
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
    (hab : BanditAlgorithm.NeighbouringActions G a b)
    (hnlocal : ¬ ∃ f : Fin k × 𝕊 → ℝ,
      BanditAlgorithm.IsLocalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, c ∈ BanditAlgorithm.pmNeighbourhood G a b → ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 :=
  BanditAlgorithm.partial_monitoring_nonlocal_edge_direction G a b hab hnlocal
