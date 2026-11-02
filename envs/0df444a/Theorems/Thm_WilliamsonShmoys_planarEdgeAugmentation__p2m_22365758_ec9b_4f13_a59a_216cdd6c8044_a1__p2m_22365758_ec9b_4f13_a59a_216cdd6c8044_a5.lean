-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEdgeAugmentation__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a5
-- name    : WilliamsonShmoys.planarEdgeAugmentation__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:13:58.43733+00:00
-- url     : https://prove2.me/theorems/75ffa561-4985-4f14-afcd-5917f3928951
-- title:
--   Planar edge augmentation below the triangulation bound
-- statement:
--   A finite drawable simple graph on at least three vertices with fewer than 3|V| − 6 edges has a drawable supergraph on the same vertex set with strictly more edges. This removes the topological extension step from the parent; a proof route extends the drawing to a maximal planar graph and uses its triangulation edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarEdgeAugmentation__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 <= Fintype.card V)
    (hcard : letI : DecidableRel G.Adj := dG
      G.edgeFinset.card < 3 * Fintype.card V - 6) :
    Exists (fun (K : SimpleGraph V) => Exists (fun (dK : DecidableRel K.Adj) =>
      HasPlanarDrawingOn K /\
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel K.Adj := dK
       G.edgeFinset ⊆ K.edgeFinset) /\
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel K.Adj := dK
       G.edgeFinset.card < K.edgeFinset.card))) := by sorry
