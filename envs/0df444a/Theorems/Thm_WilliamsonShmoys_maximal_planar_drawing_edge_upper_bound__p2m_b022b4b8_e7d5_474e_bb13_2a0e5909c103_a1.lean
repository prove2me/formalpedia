-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:45:26.355899+00:00
-- url     : https://prove2.me/theorems/b82bda5b-ef12-4d53-b93d-7cbeff7667fb
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every finite simple graph admitting the specified planar drawing, on at least three vertices, has at most 3|V|−6 edges. This is the Euler-formula upper bound; it does not assume maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by sorry
