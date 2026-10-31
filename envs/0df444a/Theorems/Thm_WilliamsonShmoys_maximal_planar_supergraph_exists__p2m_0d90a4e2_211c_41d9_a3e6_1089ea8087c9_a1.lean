-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:04.311861+00:00
-- url     : https://prove2.me/theorems/95b85285-7ea7-4e66-8526-e78475582691
-- title:
--   A finite drawable graph has a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K := by sorry
