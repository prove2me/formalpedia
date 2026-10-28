-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_extension
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:18:41.556094+00:00
-- url     : https://prove2.me/theorems/4bb87417-fcea-4413-9b9c-f7121a0b7d62
-- title:
--   A planar drawing has an edge-maximal planar supergraph
-- statement:
--   Given a finite graph with a planar drawing, choose a planar supergraph on the same vertex set that has no proper planar supergraph. The proof route is to maximize edge count among the finite set of graphs containing H that admit a drawing; any strict planar extension would have more edges. The condition |V| ≥ 3 is retained for the parent, though this finite-maximization step itself also works for smaller vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        (∀ ⦃u v : V⦄, K.Adj u v → G.Adj u v) := by sorry
