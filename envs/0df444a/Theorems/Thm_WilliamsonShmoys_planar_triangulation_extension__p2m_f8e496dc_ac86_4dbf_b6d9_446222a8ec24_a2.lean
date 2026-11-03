-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:19.456552+00:00
-- url     : https://prove2.me/theorems/ea8ef902-b5b0-4092-a824-9484bf1d76fc
-- title:
--   Drawable graphs extend to a triangulation with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on that same vertex type with exactly `3 * |V| - 6` edges. The size hypothesis includes the three-vertex boundary case, where the extension is the triangle. This child packages the geometric extension and planar edge-count argument needed by the parent; its proof route is to extend the drawing to a triangulation and count with Euler’s formula and face-edge incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le N K)
        (And (HasPlanarDrawingOn K)
          (letI : DecidableRel K.Adj := Classical.decRel K.Adj
           3 * Fintype.card V = K.edgeFinset.card + 6))) := by sorry
