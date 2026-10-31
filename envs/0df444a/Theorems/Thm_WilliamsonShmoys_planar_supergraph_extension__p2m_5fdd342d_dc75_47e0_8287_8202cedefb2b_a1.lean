-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- name    : WilliamsonShmoys.planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:29.197084+00:00
-- url     : https://prove2.me/theorems/cdaf5482-3ae6-48c3-bb07-1a30324ea07b
-- title:
--   Extend a planar graph to an inclusion-maximal planar supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex type that admits no strictly larger drawable supergraph on that type. This uses finiteness of the vertex type to maximize the edge set; it does not assume at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
