-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2
-- name    : WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:42:56.182638+00:00
-- url     : https://prove2.me/theorems/601a95aa-a232-4ea8-a05f-1a72b46d773d
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   A drawable graph on a finite vertex set with at least three vertices is contained in a drawable graph on that same vertex set that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ M : SimpleGraph V, N ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N := by
  sorry
