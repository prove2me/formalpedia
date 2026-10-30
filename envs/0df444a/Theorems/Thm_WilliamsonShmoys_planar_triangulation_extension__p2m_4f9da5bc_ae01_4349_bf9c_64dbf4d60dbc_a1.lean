-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:00:36.588582+00:00
-- url     : https://prove2.me/theorems/ef0860d4-4cfe-4ed1-9f37-9a24872db6ea
-- title:
--   Extend a planar drawing to a triangulation on the same vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T ≤ U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
