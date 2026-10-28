-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_retry_49abde41
-- name    : WilliamsonShmoys.maximal_planar_edge_count_retry_49abde41
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:05:14.123439+00:00
-- url     : https://prove2.me/theorems/08571abd-93c8-4bf4-ac16-73631fbb6ee7
-- title:
--   Edge count of an inclusion-maximal finite planar graph
-- statement:
--   If a finite simple graph has a crossing-free drawing, is inclusion-maximal among planar supergraphs on its vertex set, and has at least three vertices, then it has 3|V|−6 edges. This isolates the planar topology and edge-count argument. A proof must derive connectedness and triangular faces from maximality, establish Euler’s formula for the embedding encoded by HasPlanarDrawingOn, and count each edge twice along face boundaries. The threshold |V| ≥ 3 is needed; the geometric argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_retry_49abde41
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
