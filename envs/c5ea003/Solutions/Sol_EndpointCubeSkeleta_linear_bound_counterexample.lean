-- Prove2me | solution 1 for EndpointCubeSkeleta.linear_bound_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:34:44.486668+00:00
-- url     : https://prove2.me/submissions/0b777102-37e5-4e27-9529-3d6c6ed4828a

import Mathlib
import Definitions.Def_Cryptography_EndpointCubeSkeleta_OneDimensional
open EndpointCubeSkeleta Finset in
theorem solution :
    EndpointCovered counterexamplePoints counterexampleCenters ∧
      counterexamplePoints.card < counterexampleCenters.card := by
  refine ⟨?_, by decide⟩
  intro c hc
  simp only [counterexampleCenters, mem_insert, mem_singleton] at hc
  -- each center is the midpoint of two of the four endpoints
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by norm_num, by decide, by decide⟩
  · exact ⟨3, by norm_num, by decide, by decide⟩
  · exact ⟨2, by norm_num, by decide, by decide⟩
  · exact ⟨7, by norm_num, by decide, by decide⟩
  · exact ⟨6, by norm_num, by decide, by decide⟩
  · exact ⟨4, by norm_num, by decide, by decide⟩
