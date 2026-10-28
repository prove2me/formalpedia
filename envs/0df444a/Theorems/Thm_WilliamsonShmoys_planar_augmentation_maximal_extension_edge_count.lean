-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension_edge_count
-- name    : WilliamsonShmoys.planar_augmentation_maximal_extension_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:59:33.025222+00:00
-- url     : https://prove2.me/theorems/ad7485cc-b8d2-40e2-9994-c1ebc8aefe26
-- title:
--   Edge count of a maximal planar extension
-- statement:
--   An inclusion-maximal graph with the specified planar drawing has exactly 3|V|−6 edges when its finite vertex type has at least three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_maximal_extension_edge_count {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
