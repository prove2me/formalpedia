-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_exists__p2m_ba26c1d0_6e77_4c7c_aa33_77d1fdc6fec8_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_exists__p2m_ba26c1d0_6e77_4c7c_aa33_77d1fdc6fec8_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:23.941879+00:00
-- url     : https://prove2.me/theorems/d2c5fb5d-043b-4950-bb1e-0dd153301526
-- title:
--   Extend a nonempty planar graph to a connected planar supergraph
-- statement:
--   Every nonempty finite planar graph has a connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_exists__p2m_ba26c1d0_6e77_4c7c_aa33_77d1fdc6fec8_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn K)
    (hV : Nonempty V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.Connected ∧
      HasPlanarDrawingOn L := by
  sorry
