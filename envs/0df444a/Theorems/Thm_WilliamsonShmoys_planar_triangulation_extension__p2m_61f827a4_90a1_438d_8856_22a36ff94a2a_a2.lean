-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:21:29.733014+00:00
-- url     : https://prove2.me/theorems/2266ad6e-a873-4db0-8a1d-ced08babaea4
-- title:
--   Triangulation completion of a finite planar graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable planar supergraph on the same vertex type with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
