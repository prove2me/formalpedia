-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:42.949982+00:00
-- url     : https://prove2.me/theorems/bd9d7987-6824-4383-ac2f-f887fa429ccf
-- title:
--   Finite maximal drawable supergraph exists
-- statement:
--   Every connected drawable graph on at least three vertices has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V)
    (hConn : K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H := by sorry
