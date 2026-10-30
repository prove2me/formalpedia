-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:37:17.880746+00:00
-- url     : https://prove2.me/theorems/8a3bb09f-be34-4160-8a3f-717a48932654
-- title:
--   An inclusion-maximal planar graph has at least 3n minus 6 edges
-- statement:
--   An inclusion-maximal graph under `HasPlanarDrawingOn`, on at least three vertices, has at least 3n−6 edges. The independent route is to use maximality to connect components and rule out nontriangular faces by adding a noncrossing diagonal, then apply Euler’s formula and face-edge incidence. Together with the upper-bound child, this proves the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      (forall {u v}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
