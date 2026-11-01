-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:02.025978+00:00
-- url     : https://prove2.me/theorems/f064fab3-2a2a-43e1-9be9-e5e958f9fe83
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no strict drawable supergraph on the same vertices has exactly 3|V|−6 edges. The proof must show maximality entails a triangulation and then use Euler’s formula; the at-least-three hypothesis preserves the small-boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
