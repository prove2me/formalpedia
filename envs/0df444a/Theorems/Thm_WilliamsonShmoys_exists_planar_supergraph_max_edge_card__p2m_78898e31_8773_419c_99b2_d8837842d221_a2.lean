-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_card__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- name    : WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:28:55.79038+00:00
-- url     : https://prove2.me/theorems/2909bf9b-3247-4cf1-b481-5337b11ec489
-- title:
--   Maximum-edge planar supergraph on a finite vertex type
-- statement:
--   Among all simple graphs on the same finite ordered vertex type that contain L and satisfy the given drawing predicate, one has at least as large an edge-set cardinality as every such graph. The drawing hypothesis on L makes this family nonempty. A proof can maximize `edgeSet.ncard` over the finite type of simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard) := by sorry
