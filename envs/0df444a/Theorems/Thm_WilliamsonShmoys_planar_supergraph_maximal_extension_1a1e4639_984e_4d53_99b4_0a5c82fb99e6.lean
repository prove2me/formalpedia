-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:06:31.790187+00:00
-- url     : https://prove2.me/theorems/9388aada-df8d-48a9-a9c9-7a018ad6654e
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   On the same finite vertex type, extend the given drawable graph to a drawable graph with no strict drawable edge-set extension. A proof route chooses a maximum-edge member of the finite nonempty family of drawable supergraphs of the original graph. The hypotheses are retained from the parent theorem; the finite-maximality argument itself does not require connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊂ L.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
