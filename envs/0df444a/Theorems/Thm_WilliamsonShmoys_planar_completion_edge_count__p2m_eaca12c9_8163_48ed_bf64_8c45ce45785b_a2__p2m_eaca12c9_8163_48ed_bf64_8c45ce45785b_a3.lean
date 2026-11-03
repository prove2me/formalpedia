-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:56:50.81755+00:00
-- url     : https://prove2.me/theorems/5b23b791-8f68-4090-90fa-7eb62c80871a
-- title:
--   Drawable graphs admit an edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edgeFinset has cardinality 3|V|−6. This supplies the completion needed by the parent; the three-vertex case is included. A proof route is to augment the given drawing to a triangulation, then apply Euler’s formula and count edge-face incidences. The topological augmentation and counting argument remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
