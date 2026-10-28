-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_disconnected_drawing
-- name    : WilliamsonShmoys.exists_drawable_strict_supergraph_of_disconnected_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:43:19.506881+00:00
-- url     : https://prove2.me/theorems/34a43dbc-488e-44ec-bac5-5fafefe41c67
-- title:
--   Join distinct components by a drawable edge
-- statement:
--   A finite drawable graph with at least three vertices that is disconnected can be enlarged by a strict edge addition while remaining drawable on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_strict_supergraph_of_disconnected_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ ¬ J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
