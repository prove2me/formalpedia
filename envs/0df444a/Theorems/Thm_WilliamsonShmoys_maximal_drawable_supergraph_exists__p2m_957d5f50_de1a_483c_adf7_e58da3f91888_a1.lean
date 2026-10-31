-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:08.999573+00:00
-- url     : https://prove2.me/theorems/d962869e-258d-4947-a612-83f18b157228
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   For a finite vertex type, every graph with a planar drawing is contained in an inclusion-maximal graph with a planar drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
