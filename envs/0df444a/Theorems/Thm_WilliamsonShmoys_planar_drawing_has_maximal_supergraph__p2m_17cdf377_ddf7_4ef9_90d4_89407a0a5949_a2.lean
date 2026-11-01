-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:10:28.336412+00:00
-- url     : https://prove2.me/theorems/19dc4083-61c0-4705-828b-4b582db1bbbd
-- title:
--   A finite drawable graph has a maximal drawable supergraph
-- statement:
--   A finite drawable graph is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices. Since the vertex set is finite, choose a drawable supergraph with the maximum number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
