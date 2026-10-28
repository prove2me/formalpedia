-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_edge_lower_bound_981f13e1
-- name    : WilliamsonShmoys.maximal_edge_lower_bound_981f13e1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:17:33.982712+00:00
-- url     : https://prove2.me/theorems/d8a19633-b09c-4bba-b28e-2260bf10c995
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A graph maximal among graphs satisfying HasPlanarDrawingOn, on at least three fixed vertices, has at least 3|V|−6 edges. Prove this by showing maximality forces the connectivity and triangular-face properties needed for Euler’s formula and edge-face incidence counting. At exactly three vertices, maximality forces all three edges. This removes the maximal-planar lower-count obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_edge_lower_bound_981f13e1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → G ≤ K → K = G) :
    3 * (Fintype.card V : Int) - 6 <= (G.edgeSet.ncard : Int) := by
  sorry
