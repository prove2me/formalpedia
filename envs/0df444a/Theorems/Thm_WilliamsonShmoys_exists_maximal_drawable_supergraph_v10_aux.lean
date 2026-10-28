-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_v10_aux
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_v10_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:23:11.814981+00:00
-- url     : https://prove2.me/theorems/a9528c77-a2ec-4d50-a814-5c0008f382e0
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on that type. The finite proof route is to maximize edge count among the nonempty finite family of drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_v10_aux {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : Exists fun M : SimpleGraph V => L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M := by sorry
