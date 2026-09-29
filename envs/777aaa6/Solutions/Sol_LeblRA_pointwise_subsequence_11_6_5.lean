-- Prove2me | solution 1 for LeblRA.pointwise_subsequence_11_6_5
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:32.995588+00:00
-- url     : https://prove2.me/submissions/3d7272ee-9220-4045-9d17-1117a3191009

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

theorem solution {X : Type u} [Countable X]
    (F : ℕ → X → ℂ) (hF : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (f : X → ℂ), StrictMono φ ∧
      ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
  choose M hM using hF
  have hcompact : IsCompact (Set.pi Set.univ (fun x => Metric.closedBall (0 : ℂ) (M x))) :=
    isCompact_univ_pi fun x => isCompact_closedBall 0 (M x)
  obtain ⟨f, _, φ, hφ, hf⟩ := hcompact.tendsto_subseq (x := F) (by
    intro n x _
    simpa only [Metric.mem_closedBall, dist_zero_right] using hM x n)
  exact ⟨φ, f, hφ, fun x => (tendsto_pi_nhds.mp hf) x⟩
