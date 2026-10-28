-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_77f664a0
-- name    : WilliamsonShmoys.maximal_planar_edge_count_77f664a0
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:49:25.687619+00:00
-- url     : https://prove2.me/theorems/ee34d388-8c16-4d33-9037-8aaf2bdd5643
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under edge inclusion has exactly 3|V| − 6 edges. This isolates the geometric core: formalize faces for the given drawing predicate, show maximality forces triangular faces, and apply Euler’s formula. The hypothesis includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_77f664a0
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) →
      HasPlanarDrawingOn K →
      ∀ u v, K.Adj u v → G.Adj u v) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
