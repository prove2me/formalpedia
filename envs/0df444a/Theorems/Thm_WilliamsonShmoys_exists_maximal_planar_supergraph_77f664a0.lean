-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_77f664a0
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_77f664a0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:43:57.668978+00:00
-- url     : https://prove2.me/theorems/6160a946-0dde-4e1a-9905-399fd1381656
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion. Finiteness gives a proof route by maximizing the edge set among drawable supergraphs containing H; maximality is precisely the final quantified condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_77f664a0
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      (∀ u v, H.Adj u v → G.Adj u v) ∧
      HasPlanarDrawingOn G ∧
      (∀ K : SimpleGraph V,
        (∀ u v, G.Adj u v → K.Adj u v) →
        HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → G.Adj u v) := by sorry
