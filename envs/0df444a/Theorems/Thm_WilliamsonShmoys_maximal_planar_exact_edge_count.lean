-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:01:17.021745+00:00
-- url     : https://prove2.me/theorems/5f316376-3be4-4afa-ae0f-14ec52a7a8a1
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   An edge-maximal graph satisfying the packaged crossing-free drawing predicate, on at least three vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hMax : ∀ Z : SimpleGraph V,
      HasPlanarDrawingOn Z →
      (∀ u v, Y.Adj u v → Z.Adj u v) →
      ∀ u v, Z.Adj u v → Y.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
