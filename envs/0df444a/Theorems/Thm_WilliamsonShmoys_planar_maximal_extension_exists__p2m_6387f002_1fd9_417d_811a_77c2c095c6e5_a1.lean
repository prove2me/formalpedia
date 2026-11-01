-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:42.553452+00:00
-- url     : https://prove2.me/theorems/9642ee1f-f012-44b9-a1b9-1c78c6be4597
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
