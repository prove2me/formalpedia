-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:26.31868+00:00
-- url     : https://prove2.me/theorems/9a589b94-03d9-4778-864c-afd61c0d1307
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   A disconnected graph with at least three vertices and a crossing-free drawing can be extended, without adding vertices, to a connected graph that still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ S.Connected) :
    ∃ T : SimpleGraph V, S ≤ T ∧ T.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn T := by sorry
