-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:07:11.000461+00:00
-- url     : https://prove2.me/theorems/5f80b45b-1b9e-4ccf-a15d-46b44714c5e2
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is inclusion-maximal among drawable supergraphs. The independent proof route is to maximize edge count over the finite family of drawable supergraphs containing the given graph, then use strict edge-count growth for a proper extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
