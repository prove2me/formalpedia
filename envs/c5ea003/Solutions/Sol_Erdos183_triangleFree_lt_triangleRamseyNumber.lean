-- Prove2me | solution 1 for Erdos183.triangleFree_lt_triangleRamseyNumber
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:23:18.525979+00:00
-- url     : https://prove2.me/submissions/edacbe41-a8a2-41a2-9591-9110d4aed1e4

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Theorems.Thm_Erdos183_cliqueFree_pullback_embedding
import Theorems.Thm_Erdos183_triangleRamseyNumber_forces

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem forcesMonochromaticTriangle_mono {m n k : ℕ}
    (hmn : m ≤ n) (hm : ForcesMonochromaticTriangle m k) :
    ForcesMonochromaticTriangle n k := by
  intro C hC
  exact hm (C.pullback (Fin.castLEEmb hmn))
    (cliqueFree_pullback_embedding C (Fin.castLEEmb hmn) hC)

end Erdos183

open Erdos183

theorem solution {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k))
    (hC : TriangleFree C) :
    n < triangleRamseyNumber k := by
  by_contra hnot
  have hle : triangleRamseyNumber k ≤ n := by omega
  have hforcing : ForcesMonochromaticTriangle n k :=
    forcesMonochromaticTriangle_mono hle
      (triangleRamseyNumber_forces k)
  exact hforcing C hC
