-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
-- name    : WilliamsonShmoys.planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:45.055002+00:00
-- url     : https://prove2.me/theorems/a475315c-2c4b-45b0-9566-59ca0c26cf0a
-- title:
--   Finite termination of planar edge augmentation
-- statement:
--   On a fixed finite vertex type, a planar edge-growth step that applies to every disconnected drawing can be iterated to produce a connected planar supergraph. This packages the finite edge-bound termination argument and monotonicity of edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (step : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ HasPlanarDrawingOn K ∧
        G.edgeSet.ncard < K.edgeSet.ncard)
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard <= K.edgeSet.ncard ∧
      HasPlanarDrawingOn K ∧ K.Connected := by sorry
