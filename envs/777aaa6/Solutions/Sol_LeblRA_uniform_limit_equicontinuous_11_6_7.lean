-- Prove2me | solution 1 for LeblRA.uniform_limit_equicontinuous_11_6_7
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:34.303067+00:00
-- url     : https://prove2.me/submissions/fc71a8c3-9e52-46a6-b5e7-9cbd3acc5168

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
    (F : ℕ → X → ℂ) (hF : ∀ n, Continuous (F n)) (f : X → ℂ)
    (hf : TendstoUniformly F f atTop) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ n, ‖F n x - F n y‖ < ε := by
  let G : ℕ → C(X, ℂ) := fun n => ⟨F n, hF n⟩
  let g : C(X, ℂ) := ⟨f, hf.continuous (Filter.Frequently.of_forall hF)⟩
  have hg : Tendsto G atTop (𝓝 g) := ContinuousMap.tendsto_iff_tendstoUniformly.mpr hf
  let K : Set C(X, ℂ) := insert g (range G)
  have hK : IsCompact K := hg.isCompact_insert_range
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heval : Continuous (fun p : K × X => (p.1 : C(X, ℂ)) p.2) :=
    (continuous_subtype_val.comp continuous_fst).eval continuous_snd
  have huc := CompactSpace.uniformContinuous_of_continuous heval
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy n
  let k : K := ⟨G n, Or.inr (mem_range_self n)⟩
  have hd : dist (k, x) (k, y) < δ := by simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hxy
  simpa only [dist_eq_norm] using h hd
