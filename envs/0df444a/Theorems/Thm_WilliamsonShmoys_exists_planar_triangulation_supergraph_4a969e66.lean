-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_4a969e66
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_4a969e66
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:12:40.554665+00:00
-- url     : https://prove2.me/theorems/d090e857-babc-4b1f-b4be-f9067d451864
-- title:
--   Planar triangulation augmentation on the same vertex set
-- statement:
--   Any graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three is a subgraph of a drawable graph on the same vertex type with exactly 3n − 6 edges. The child preserves the vertex-count lower bound and drawing hypotheses needed for the augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_4a969e66
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
