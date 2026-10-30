-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_repair_20261028
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_repair_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:18:32.156157+00:00
-- url     : https://prove2.me/theorems/465e1a5c-4eab-4c72-b9fc-e7b20ecb827b
-- title:
--   Connect a finite graph while preserving its drawing
-- statement:
--   This child removes the work of handling disconnected graphs from the parent. It is a new topological argument: repeatedly join distinct drawn components by an arc through a face, with the arc interior avoiding the existing drawing and all vertices. The same vertex set is retained, and the three-vertex hypothesis is preserved. A proof must verify that each added arc satisfies the exact intersection and endpoint conditions in `HasPlanarDrawingOn`; the supplied notes do not establish this step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_repair_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
