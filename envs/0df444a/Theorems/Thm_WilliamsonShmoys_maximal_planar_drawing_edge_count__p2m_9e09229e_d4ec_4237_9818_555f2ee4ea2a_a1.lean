-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:03.280954+00:00
-- url     : https://prove2.me/theorems/f90853da-a441-4590-8374-63300059b95b
-- title:
--   Maximal drawable graphs with at least three vertices have the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
