-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_retry_49abde41
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_49abde41
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:31:25.388537+00:00
-- url     : https://prove2.me/theorems/bba80254-5774-4136-a3af-a4166fc404cd
-- title:
--   An inclusion-maximal planar graph has at least 3n − 6 edges
-- statement:
--   A graph with this crossing-free drawing that is maximal among planar supergraphs on the same vertices, and has at least three vertices, has at least `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_49abde41
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    (H.edgeSet.ncard : Int) >= 3 * (Fintype.card V : Int) - 6 := by sorry
