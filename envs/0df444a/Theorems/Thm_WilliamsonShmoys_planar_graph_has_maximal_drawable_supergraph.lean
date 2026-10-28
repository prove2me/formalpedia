-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:28:40.332724+00:00
-- url     : https://prove2.me/theorems/8f4a7131-6c4a-423c-9f8d-403e61501fbb
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   A drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        ∀ Q : SimpleGraph V,
          P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by sorry
