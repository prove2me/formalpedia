-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:24.634987+00:00
-- url     : https://prove2.me/theorems/3a2fa668-af0b-4223-89b0-dcabec19097b
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that has no drawable supergraph with more edges has exactly three times the number of vertices minus six edges. The anchor inclusion records that this graph is an extension in the augmentation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (A N : SimpleGraph V)
    (hAN : A ≤ N)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
