-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- name    : WilliamsonShmoys.planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:08.816685+00:00
-- url     : https://prove2.me/theorems/75c4b74b-9a95-45f1-bc47-d23d1c54d3d8
-- title:
--   Existence of an inclusion-maximal planar extension
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex set that is maximal under edge-set inclusion among drawable graphs. Choose a graph with maximum edge count from the finite collection of drawable supergraphs containing L. The collection is nonempty because it contains L. This separates finite selection from the topological argument; disconnected inputs and isolated vertices are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M ∧
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) ∧
      (∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
        HasPlanarDrawingOn N →
        (letI : DecidableRel M.Adj := dM
         letI : DecidableRel N.Adj := dN
         M.edgeFinset ⊆ N.edgeFinset) →
        (letI : DecidableRel M.Adj := dM
         letI : DecidableRel N.Adj := dN
         N.edgeFinset ⊆ M.edgeFinset)) := by sorry
