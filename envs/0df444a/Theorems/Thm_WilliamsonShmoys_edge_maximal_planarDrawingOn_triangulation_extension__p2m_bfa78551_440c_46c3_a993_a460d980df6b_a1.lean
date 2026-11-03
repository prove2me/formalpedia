-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
-- name    : WilliamsonShmoys.edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:23.193489+00:00
-- url     : https://prove2.me/theorems/e8d3fd6d-990f-43df-873b-df1b4f477345
-- title:
--   Planar triangulation extension on a fixed vertex set
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. This is the triangulation-extension theorem for the target's arc-based definition of a planar drawing. The claim covers the equality boundary |V| = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel H.Adj := dH;
       letI : DecidableRel K.Adj := dK;
       H.edgeFinset ⊆ K.edgeFinset ∧
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
