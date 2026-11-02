-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:45.687213+00:00
-- url     : https://prove2.me/theorems/eb4e4f8a-f0d0-4555-99e8-d1873b30ad40
-- title:
--   A finite planar supergraph can be chosen maximal
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs on those vertices. This removes the finite edge-selection step from the parent. A proof route is to maximize the edge count among the finite set of supergraphs that contain H and admit a drawing; any drawable supergraph of a maximizer must have the same edges and hence be equal. This statement needs no lower bound on the number of vertices; that hypothesis is used by the edge-count child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) [DecidableRel H.Adj] (hH : HasPlanarDrawingOn H) : ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj), H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ (L : SimpleGraph V) [DecidableRel L.Adj], K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
