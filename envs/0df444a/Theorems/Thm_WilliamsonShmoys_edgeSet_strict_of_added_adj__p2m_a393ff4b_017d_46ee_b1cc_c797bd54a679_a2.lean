-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2
-- name    : WilliamsonShmoys.edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:57.006723+00:00
-- url     : https://prove2.me/theorems/381fb172-9839-4a61-b336-6fdc726bc55d
-- title:
--   A new adjacency makes edge-set inclusion strict
-- statement:
--   If `K`’s edges are included in `M`, and `M` has an edge between vertices that are not reachable in `K`, then `M`’s edge set is not included in `K`’s edge set. This isolates the graph-theoretic strictness step from the planar construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K M : SimpleGraph V)
    (hsub : K.edgeSet ⊆ M.edgeSet)
    {u v : V}
    (hMuv : M.Adj u v)
    (huv : ¬ K.Reachable u v) :
    ¬ M.edgeSet ⊆ K.edgeSet := by sorry
