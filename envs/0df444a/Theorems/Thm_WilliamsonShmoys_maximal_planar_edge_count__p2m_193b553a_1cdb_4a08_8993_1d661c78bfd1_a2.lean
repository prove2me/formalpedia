-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:30.105981+00:00
-- url     : https://prove2.me/theorems/df7ea954-0a80-4086-897f-2a8fe8c6b2c5
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-maximal planar simple graph on at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L.edgeFinset = K.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
