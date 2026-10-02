-- Prove2me | Theorems.Thm_Arexychen_Erdos180_exists_maximalMatching_edgeCover
-- name    : Arexychen.Erdos180.exists_maximalMatching_edgeCover
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:34.368881+00:00
-- url     : https://prove2.me/theorems/29727999-b8d4-400c-b068-d23cdf08df26
-- title:
--   A maximal matching supplies an edge-covering vertex set
-- statement:
--   Every simple graph $G$ on $\operatorname{Fin}(n)$, for any natural $n$, has a matching subgraph $M$ maximal among matching subgraphs under inclusion, whose vertex set meets every edge of $G$. The statement requires no supplied decision procedure for adjacency and includes the empty host graph.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Upper.lean#L113-L147

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w

theorem Arexychen.Erdos180.exists_maximalMatching_edgeCover
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
        Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
          ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ M.verts ∨ y ∈ M.verts := by sorry
