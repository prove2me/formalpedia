-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:40:54.28299+00:00
-- url     : https://prove2.me/theorems/a8d4ac35-97b5-4704-9d15-83af1a845a7a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable proper supergraph on the same vertex type has exactly `3 * (|V| - 2)` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard = 3 * (Fintype.card V - 2) := by sorry
