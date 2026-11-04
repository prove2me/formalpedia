-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:36.042265+00:00
-- url     : https://prove2.me/theorems/75881c5e-3a5f-4c38-b417-ac584a1894e5
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has at least 3|V|−6 edges. This removes the maximality-based lower-bound direction from the parent. A proof route uses maximality to rule out disconnected components and nontriangular faces, then applies Euler’s formula and face-edge incidence. The remaining core obligation is formalizing those topological consequences for the supplied arc-based drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeFinset.card + 6 := by sorry
