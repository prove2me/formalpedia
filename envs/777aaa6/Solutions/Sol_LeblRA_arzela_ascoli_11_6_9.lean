-- Prove2me | solution 1 for LeblRA.arzela_ascoli_11_6_9
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:35.460282+00:00
-- url     : https://prove2.me/submissions/078de6f9-4ce0-4a1e-aae1-961505bf17c5

import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
open Filter Set Topology
open scoped UniformConvergence
universe u

theorem solution {X : Type u} [MetricSpace X] [CompactSpace X]
    (F : ℕ → X → ℂ) (hF : ∀ n, Continuous (F n))
    (hb : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M)
    (he : ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ n, ‖F n x - F n y‖ < ε) :
    (∃ M : ℝ, ∀ n x, ‖F n x‖ ≤ M) ∧
    ∃ (φ : ℕ → ℕ) (f : X → ℂ), StrictMono φ ∧ Continuous f ∧
      TendstoUniformly (fun n => F (φ n)) f atTop := by
  let G : ℕ → C(X, ℂ) := fun n => ⟨F n, hF n⟩
  have he' : Equicontinuous F := (Metric.uniformEquicontinuous_iff.mpr (by
    simpa only [dist_eq_norm] using he)).equicontinuous
  letI : T2Space (X →ᵤ[{K : Set X | IsCompact K}] ℂ) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure (range G)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X, ℂ) => (g : X → ℂ))
      (𝔖 := {s : Set X | IsCompact s})
      (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have h : Equicontinuous (fun g : range G => ((g : C(X, ℂ)) : X → ℂ)) := by
        classical
        have hx := he'.comp (fun g : range G => g.property.choose)
        convert hx using 1
        funext g x
        exact congrArg (fun p : C(X, ℂ) => p x) g.property.choose_spec.symm
      exact h.equicontinuousOn K
    · intro K hK x hx
      obtain ⟨M, hM⟩ := hb x
      refine ⟨Metric.closedBall 0 M, isCompact_closedBall _ _, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hM n
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  constructor
  · refine ⟨M, fun n x => le_trans ((G n).norm_coe_le_norm x) ?_⟩
    exact hM _ (subset_closure (mem_range_self n))
  · obtain ⟨g, _, φ, hφ, hg⟩ := hc.tendsto_subseq (x := G) (fun n => subset_closure (mem_range_self n))
    exact ⟨φ, g, hφ, g.continuous, ContinuousMap.tendsto_iff_tendstoUniformly.mp hg⟩
