-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:06.230026+00:00
-- url     : https://prove2.me/theorems/eacf956f-cefb-4210-bf9e-9cc0b6fb5cbc
-- title:
--   Choose an edge-maximal planar supergraph
-- statement:
--   Among the finitely many simple graphs on V that contain K and have a planar drawing, choose one maximal under graph inclusion. Its edge set contains K’s, so its edge count is at least K’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
