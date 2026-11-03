-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:51.431475+00:00
-- url     : https://prove2.me/theorems/71c4bf82-58f5-4c33-a47c-7b17640d4f06
-- title:
--   Extend a drawable graph to an exact-count triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices whose edge count is 3|V|−6. This removes the parent’s maximality assumption and supplies the triangulation extension needed to derive its conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    Exists (fun N : SimpleGraph V => M <= N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
       N.edgeFinset.card + 6 = 3 * Fintype.card V)) := by sorry
