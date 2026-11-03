-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- name    : WilliamsonShmoys.planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:48.604975+00:00
-- url     : https://prove2.me/theorems/0ab193fe-0f8a-4383-a58d-9f4c1a7627f8
-- title:
--   Extension of a planar graph to a triangulation
-- statement:
--   Any finite simple graph drawable without crossings on a fixed vertex set of size at least three has a planar supergraph on that same vertex set with exactly 3|V|−6 edges. This preserves the vertex set and the original edge set, including when the original graph is disconnected or has isolated vertices. An independent proof route is to add noncrossing edges until the drawing is inclusion-maximal, show the resulting embedding is connected and every face is triangular, and count incidences using Euler’s formula. This is the geometric extension step; its proof must justify that the process can continue on the fixed finite vertex set and handle the boundary case |V|=3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M ∧
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) ∧
      (letI : DecidableRel M.Adj := dM
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
