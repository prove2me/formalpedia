-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:12.707668+00:00
-- url     : https://prove2.me/theorems/b704201f-fc6b-4e4c-b576-9e83647d88b7
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A finite simple graph with a crossing-free drawing, at least three vertices, and no strictly larger drawable simple supergraph has at least 3n−6 edges. This isolates the maximality-to-triangulation step. In an embedding, a face with more than three boundary vertices admits a missing diagonal drawn in that face; maximality rules this out. Thus the embedding is triangulated, and Euler’s formula yields the lower bound. For n=3 the bound is zero and remains valid.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
