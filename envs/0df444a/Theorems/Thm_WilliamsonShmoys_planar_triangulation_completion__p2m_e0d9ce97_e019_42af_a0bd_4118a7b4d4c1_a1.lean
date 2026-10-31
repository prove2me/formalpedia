-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:55.138696+00:00
-- url     : https://prove2.me/theorems/686fb965-c7d3-49a9-b66b-5594659aa3e2
-- title:
--   Planar graph completion to the maximal edge count
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex set of size at least three is a subgraph of a planar graph on that same vertex set with exactly 3|V|−6 edges. At the boundary |V|=3, this is consistent with completion to K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := dH
     ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
       H <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
       (letI : DecidableRel L.Adj := dL
        L.edgeFinset.card = 3 * Fintype.card V - 6)) := by sorry
