-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:17.514947+00:00
-- url     : https://prove2.me/theorems/56b77430-5edc-41bf-8724-d4c1ab81c0d8
-- title:
--   Triangulated planar supergraph on the same finite vertex set
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertex set whose edge count satisfies 3|V| = |E| + 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * Fintype.card V =
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card) + 6 := by sorry
