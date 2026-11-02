-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:38:40.843229+00:00
-- url     : https://prove2.me/theorems/160c891e-c18d-4863-b495-0a238ee51219
-- title:
--   Planar triangulation extension edge bound
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
       3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by sorry
