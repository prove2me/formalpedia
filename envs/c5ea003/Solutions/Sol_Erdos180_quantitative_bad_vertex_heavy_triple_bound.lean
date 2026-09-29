-- Prove2me | solution 1 for Erdos180.quantitative_bad_vertex_heavy_triple_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:02:24.865099+00:00
-- url     : https://prove2.me/submissions/19e80717-e45d-4f86-8cab-ba07bf3f9457

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Theorems.Thm_Erdos180_gammaBad_card_mul_fourpath_power_le

open Erdos180
open Finset SimpleGraph

theorem solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
      432 * (n : ℝ) ^ 5 := by
  apply (mul_le_mul_iff_right₀
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  exact_mod_cast Nat.mul_le_mul_left n
    (gammaBad_card_mul_fourpath_power_le
      host hfree hbip d hdegree hthreshold)
