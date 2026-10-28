-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_pair_extension_cert38ffb807
-- name    : WilliamsonShmoys.planar_drawing_pair_extension_cert38ffb807
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:30:31.356023+00:00
-- url     : https://prove2.me/theorems/fdf3ccb1-c82f-4ece-a6f5-1d1d9590f274
-- title:
--   Planar drawing extension connecting a disconnected pair
-- statement:
--   Extend a finite planar graph by an edge joining any two distinct vertices from different connected components, while retaining a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_pair_extension_cert38ffb807
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v)
    (hnot : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Relation.ReflTransGen H.Adj u v := by
  sorry
