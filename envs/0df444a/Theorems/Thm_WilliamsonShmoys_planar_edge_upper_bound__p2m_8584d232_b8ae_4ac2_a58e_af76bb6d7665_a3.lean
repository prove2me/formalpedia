-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:15.859425+00:00
-- url     : https://prove2.me/theorems/4ab90c81-e0ae-42fd-86c7-d03618200022
-- title:
--   Planar edge upper bound
-- statement:
--   Any graph with the supplied planar drawing and at least three vertices has at most 3|V|−6 edges. This removes the upper-bound direction from the parent. A proof route augments the graph, on the same finite vertex set, to a maximal planar supergraph and applies Euler’s formula and the triangular-face incidence count. The remaining work is to formalize planar augmentation and its preservation of the drawing relation; the lower bound for the parent is not established by this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
