-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
-- name    : WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:35.714751+00:00
-- url     : https://prove2.me/theorems/a76ab648-9831-4644-9b76-244e5b3cfa82
-- title:
--   A maximal drawable graph on a nonempty finite vertex set is connected
-- statement:
--   If a finite nonempty graph has a crossing-free drawing and no drawable supergraph on the same vertex set can strictly extend its edge set, then the graph is connected. For one vertex, connectedness holds directly. Otherwise, the proof route is to join vertices in distinct components by an arc through a common face of the drawing, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 1 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax :
      ∀ M : SimpleGraph V,
        K.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ K.edgeSet) :
    K.Connected := by sorry
