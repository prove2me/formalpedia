-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:57:19.233975+00:00
-- url     : https://prove2.me/theorems/be41326b-b517-4440-a003-0c871cf552d0
-- title:
--   Monotonicity of simple graph edge counts
-- statement:
--   If one simple graph is a subgraph of another on the same finite vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
