-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:54:42.87086+00:00
-- url     : https://prove2.me/theorems/3e20b199-32f9-4aa6-83e2-00145d2a7578
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The size hypothesis is essential to the usual maximal-planar count and is preserved explicitly; at |V|=3 the claim gives three edges. A proof route is to show maximality forces connectivity and triangular faces, and then count edges using Euler’s formula. This child isolates the remaining topological core rather than restating the parent, and its exact drawing predicate must be related rigorously to the planar embedding and face arguments.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
