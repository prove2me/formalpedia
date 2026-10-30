-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_completion
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:34:13.553823+00:00
-- url     : https://prove2.me/theorems/42bc4921-e1fc-4b57-9208-9a2e0668df27
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph maximal under edge inclusion has exactly 3|V|−6 edges when |V|≥3. This child removes the Euler-counting step from the parent and preserves the required lower bound. A proof route is to show maximality forces a triangulation of the sphere, then apply Euler’s formula and count face-edge incidences. The case |V|=3 is included; the hypothesis excludes the smaller cases where this formula need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn U →
      ∀ {u v}, U.Adj u v → T.Adj u v) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
