-- Prove2me | solution 1 for KServer.two_server_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:36:38.368494+00:00
-- url     : https://prove2.me/submissions/4149d355-e631-4c94-89ed-011226c9a052

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_two_server_inj
import Theorems.Thm_KServer_injective_or_covering
import Theorems.Thm_KServer_competitive_of_covering_config

open KServer

/-- Two servers: the Work Function Algorithm is `2`-competitive on every metric space.
This is the Extended Cost Lemma applied with `lam = 3`, together with the degenerate case
in which the space has at most two points covered at once. -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 2 M) :
    ∃ A : OnlineAlgorithm 2 M, A.conf [] = C₀ ∧ IsCompetitive A 2 := by
  rcases injective_or_covering 2 M C₀ with ⟨X₀, hX₀⟩ | ⟨Y, hY⟩
  · obtain ⟨c, hgrowth⟩ := workFnU_growth_two_server_inj M C₀
    obtain ⟨A, hA0, hA⟩ :=
      extended_cost_lemma_injective 2 (by norm_num) M C₀ X₀ hX₀ 3 c hgrowth
    refine ⟨A, hA0, ?_⟩
    have e : (3 : ℝ) - 1 = 2 := by norm_num
    rwa [e] at hA
  · exact competitive_of_covering_config 2 M C₀ Y hY 2 (by norm_num)
