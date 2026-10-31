-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:56.80703+00:00
-- url     : https://prove2.me/theorems/c28c5998-faac-44a3-b6f1-2a93fc56a9eb
-- title:
--   Planar extension with the maximal planar edge count
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices is contained in a graph on the same vertices that has a crossing-free drawing and exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
