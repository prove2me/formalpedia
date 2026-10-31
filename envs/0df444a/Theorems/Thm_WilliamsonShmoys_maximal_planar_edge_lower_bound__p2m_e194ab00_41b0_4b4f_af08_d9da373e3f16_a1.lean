-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:07.816991+00:00
-- url     : https://prove2.me/theorems/75785758-9f27-4736-ab49-77b09febfcc3
-- title:
--   Edge lower bound for a maximal planar graph
-- statement:
--   A graph maximal among the graphs on the same vertex type admitting a drawing satisfying HasPlanarDrawingOn has at least 3|V| − 6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
