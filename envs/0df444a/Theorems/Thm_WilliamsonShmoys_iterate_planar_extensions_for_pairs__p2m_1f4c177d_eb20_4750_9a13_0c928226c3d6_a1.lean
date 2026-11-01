-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_planar_extensions_for_pairs__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- name    : WilliamsonShmoys.iterate_planar_extensions_for_pairs__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:46.090128+00:00
-- url     : https://prove2.me/theorems/d6f5c40d-4678-423c-a95b-17addb4a7c75
-- title:
--   Iterate planar extensions over a finite list of vertex pairs
-- statement:
--   For any finite list of vertex pairs, a planar graph can be extended to a planar supergraph in which every listed pair is reachable, assuming each planar graph can be extended to join any currently unreachable pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.iterate_planar_extensions_for_pairs__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hstep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ u v : V, ¬ G.Reachable u v →
        ∃ K : SimpleGraph V,
          HasPlanarDrawingOn K ∧ G ≤ K ∧ K.Adj u v)
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (pairs : List (V × V)) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G ≤ H ∧ ∀ p ∈ pairs, H.Reachable p.1 p.2 := by sorry
