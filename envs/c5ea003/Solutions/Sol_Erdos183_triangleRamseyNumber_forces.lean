-- Prove2me | solution 1 for Erdos183.triangleRamseyNumber_forces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:21:55.13955+00:00
-- url     : https://prove2.me/submissions/e173d3f2-d3d8-4782-814d-0718ffe10296

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Data.Nat.Lattice
import Theorems.Thm_Erdos183_forcesMonochromaticTriangle_succ
import Theorems.Thm_Erdos183_forcesMonochromaticTriangle_zero

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem exists_forcesMonochromaticTriangle (k : ℕ) :
    ∃ n : ℕ, ForcesMonochromaticTriangle n k := by
  induction k with
  | zero =>
      exact ⟨2, forcesMonochromaticTriangle_zero⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨1 + (k + 1) * n, forcesMonochromaticTriangle_succ hn⟩

end Erdos183

open Erdos183

theorem solution (k : ℕ) :
    ForcesMonochromaticTriangle (triangleRamseyNumber k) k := by
  exact Nat.sInf_mem (exists_forcesMonochromaticTriangle k)
