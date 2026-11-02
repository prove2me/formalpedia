-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:33:33.313307+00:00
-- url     : https://prove2.me/theorems/0a2f9458-d7af-417f-8026-7751bf7a2ead
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) : ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj), K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj), L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
