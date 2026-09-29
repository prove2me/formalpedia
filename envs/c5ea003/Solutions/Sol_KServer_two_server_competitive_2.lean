-- Prove2me | solution 2 for KServer.two_server_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:17:30.184522+00:00
-- url     : https://prove2.me/submissions/e09e5e1a-9d3d-4e9d-80c9-c0de71566f69

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_injective_or_covering
import Theorems.Thm_KServer_competitive_of_covering_config
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_two_server_inj

open KServer

/-- **The k-server conjecture for two servers.** On every metric space and from every
initial configuration there is a `2`-competitive deterministic online 2-server
algorithm: the Extended Cost Lemma applied with `lam = 3`. -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 2 M) :
    ∃ A : OnlineAlgorithm 2 M, A.conf [] = C₀ ∧ IsCompetitive A 2 := by
  classical
  rcases injective_or_covering 2 M C₀ with ⟨X₀, hX₀⟩ | ⟨Y, hY⟩
  · obtain ⟨c, hgrowth⟩ := workFnU_growth_two_server_inj M C₀
    obtain ⟨A, hA0, hA⟩ :=
      extended_cost_lemma_injective 2 (by norm_num) M C₀ X₀ hX₀ 3 c hgrowth
    refine ⟨A, hA0, ?_⟩
    have e : (3:ℝ) - 1 = 2 := by norm_num
    rwa [e] at hA
  · exact competitive_of_covering_config 2 M C₀ Y hY 2 (by norm_num)
