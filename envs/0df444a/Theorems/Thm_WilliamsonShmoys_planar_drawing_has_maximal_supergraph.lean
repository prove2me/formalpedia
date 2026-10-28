-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:06:34.971831+00:00
-- url     : https://prove2.me/theorems/e7e5f403-9eeb-46b0-917e-300e3051e9a8
-- title:
--   A planar drawing has an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph has a planar supergraph on the same vertices that admits no proper planar supergraph. Since there are finitely many simple graphs on the fixed vertex type, one can ascend among planar supergraphs until reaching a maximal one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn G → G = H) := by sorry
