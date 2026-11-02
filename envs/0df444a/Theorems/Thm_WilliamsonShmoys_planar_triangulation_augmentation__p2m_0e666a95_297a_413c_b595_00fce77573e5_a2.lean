-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_augmentation__p2m_0e666a95_297a_413c_b595_00fce77573e5_a2
-- name    : WilliamsonShmoys_planar_triangulation_augmentation__p2m_0e666a95_297a_413c_b595_00fce77573e5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:36.077956+00:00
-- url     : https://prove2.me/theorems/a54445f0-0fb5-40fc-985c-d49e2ad2f1c5
-- title:
--   Same-vertex planar triangulation augmentation
-- statement:
--   Any connected drawable graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_planar_triangulation_augmentation__p2m_0e666a95_297a_413c_b595_00fce77573e5_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hconn : M.Connected) : ∃ (N : SimpleGraph V), ∃ (dN : DecidableRel N.Adj), M <= N ∧ HasPlanarDrawingOn N ∧ (letI : DecidableRel N.Adj := dN; 3 * Fintype.card V = N.edgeFinset.card + 6) := by sorry
