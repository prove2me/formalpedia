-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:08:29.500043+00:00
-- url     : https://prove2.me/theorems/19c54c4c-0496-4f77-addb-9644187ccdaf
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same type. This reduces choosing an extension to a finite maximization over possible edge sets; it does not assert a lower bound on the selected graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      LE.le K L ∧
      HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, LE.le L M → HasPlanarDrawingOn M → LE.le M L := by sorry
