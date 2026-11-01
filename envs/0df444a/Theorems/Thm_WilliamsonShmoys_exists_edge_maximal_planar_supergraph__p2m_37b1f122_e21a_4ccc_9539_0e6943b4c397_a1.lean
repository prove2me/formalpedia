-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:18.999711+00:00
-- url     : https://prove2.me/theorems/65144f9b-062d-49b2-8349-18e0af58320c
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by sorry
