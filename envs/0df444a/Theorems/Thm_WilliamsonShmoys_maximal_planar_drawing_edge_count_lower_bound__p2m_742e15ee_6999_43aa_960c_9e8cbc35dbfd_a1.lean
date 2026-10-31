-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:16.632433+00:00
-- url     : https://prove2.me/theorems/9379b763-2dc6-43e2-b02a-b18a7334854d
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   An inclusion-maximal graph with the given planar drawing, on at least three finite vertices, has at least 3|V|−6 edges. The proof route establishes that maximality rules out nontriangular faces because a missing drawable edge could be added, then uses Euler’s formula and face-edge incidence to obtain the lower bound. The size condition handles the small boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
