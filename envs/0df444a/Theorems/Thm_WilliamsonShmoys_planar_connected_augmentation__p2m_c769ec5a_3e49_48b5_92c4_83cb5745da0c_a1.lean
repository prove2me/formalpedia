-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- name    : WilliamsonShmoys.planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:21.730102+00:00
-- url     : https://prove2.me/theorems/3d18ba84-dae9-4abe-9f72-3fa917a9726c
-- title:
--   Connected planar augmentation without decreasing edge count
-- statement:
--   A drawable finite simple graph on at least three vertices has a connected drawable supergraph on the same vertex set whose edge count is at least as large. This isolates the disconnected case: connect the components while preserving planarity and the existing edges. A proof route is to join components through the complement of the finite drawing, then establish connectedness and edge-count monotonicity. The size hypothesis excludes the empty and small-vertex cases that invalidate unrestricted augmentation claims.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard <= K.edgeSet.ncard ∧
      HasPlanarDrawingOn K ∧ K.Connected := by sorry
