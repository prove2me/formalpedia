-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:30.850465+00:00
-- url     : https://prove2.me/theorems/880bebe9-1983-4c6f-a379-091476559c81
-- title:
--   Planar supergraph maximal under edge inclusion
-- statement:
--   A finite planar graph with at least three vertices has a planar supergraph on the same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      Exists fun dK : DecidableRel K.Adj =>
        And (H.edgeFinset ⊆ K.edgeFinset)
          (And (WilliamsonShmoys.HasPlanarDrawingOn K)
            (forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
              K.edgeFinset ⊆ L.edgeFinset ->
              WilliamsonShmoys.HasPlanarDrawingOn L ->
              L.edgeFinset = K.edgeFinset)) := by sorry
