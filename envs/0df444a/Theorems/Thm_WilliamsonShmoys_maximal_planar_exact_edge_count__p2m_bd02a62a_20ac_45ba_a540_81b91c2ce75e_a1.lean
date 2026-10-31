-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:45.036169+00:00
-- url     : https://prove2.me/theorems/db7ffdc7-d913-4822-af5b-b88ad4555746
-- title:
--   Maximal drawable graphs have the planar edge count
-- statement:
--   A graph drawable by the supplied crossing-free arc data that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges when |V|≥3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
