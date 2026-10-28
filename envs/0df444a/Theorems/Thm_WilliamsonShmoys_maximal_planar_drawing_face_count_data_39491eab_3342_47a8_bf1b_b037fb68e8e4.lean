-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:03:17.37598+00:00
-- url     : https://prove2.me/theorems/355b5b28-afa9-40cf-a029-75a567b1d1a2
-- title:
--   Face-count data for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has finite face-count data satisfying Euler’s relation, edge-side double counting, and triangular face lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    Nonempty (WilliamsonShmoys.PlanarFaceCountData K) := by sorry
