-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:12.187686+00:00
-- url     : https://prove2.me/theorems/d414e93e-8443-4d15-9623-1bfdbaebf7cf
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every graph with a planar drawing on a finite linearly ordered vertex type of size at least three has at most 3|V|−6 edges. This isolates the Euler-formula upper bound from maximality. The lower-size boundary is excluded by the explicit hypothesis |V|≥3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
