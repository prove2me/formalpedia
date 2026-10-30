-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:50.915558+00:00
-- url     : https://prove2.me/theorems/8cf62bec-83fd-4fe0-af2f-abcdf3504431
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Among the finitely many drawable supergraphs of K on V, there is one maximal by graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
