-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
-- name    : WilliamsonShmoys.planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:23.196486+00:00
-- url     : https://prove2.me/theorems/52d80640-fd16-42f7-b63d-2010f98eda2f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every simply drawable graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
