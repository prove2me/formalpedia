-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:08.57389+00:00
-- url     : https://prove2.me/theorems/4553358e-4865-4072-b187-cda5e04dbc8a
-- title:
--   Edge count of a maximal simple planar graph
-- statement:
--   A simple graph that is maximal among planar supergraphs on the same vertex set, with at least three vertices, has exactly 3|V|−6 edges. The standard route is to use the planar embedding’s faces, show maximality forces triangular faces, and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
