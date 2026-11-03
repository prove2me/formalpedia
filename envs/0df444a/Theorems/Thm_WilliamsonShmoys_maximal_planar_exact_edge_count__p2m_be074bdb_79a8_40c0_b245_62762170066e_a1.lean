-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:57.532854+00:00
-- url     : https://prove2.me/theorems/5324d67d-14ae-438c-82d4-e1293378ffbf
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on a finite linearly ordered vertex type that cannot be enlarged while remaining drawable has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := dK;
      3 * Fintype.card V - 6 = K.edgeFinset.card) := by sorry
