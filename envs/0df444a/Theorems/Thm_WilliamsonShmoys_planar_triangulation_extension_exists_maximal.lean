-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exists_maximal
-- name    : WilliamsonShmoys.planar_triangulation_extension_exists_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:45:51.242155+00:00
-- url     : https://prove2.me/theorems/91fb7d9c-fd87-4703-bf10-7088d20c124e
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_exists_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V,
        (∀ u v, L.Adj u v → M.Adj u v) →
        HasPlanarDrawingOn M →
        ∀ u v, M.Adj u v → L.Adj u v) := by sorry
