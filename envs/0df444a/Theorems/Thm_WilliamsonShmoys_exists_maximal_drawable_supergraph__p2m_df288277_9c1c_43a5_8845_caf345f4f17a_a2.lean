-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:23:11.648555+00:00
-- url     : https://prove2.me/theorems/9e204529-30ef-4a52-ac3c-8c5d29c28d5c
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex set has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs. Prove this by maximizing the edge count over the finite nonempty family of drawable supergraphs containing the original graph; a strict extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (G : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph S, G ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph S, N ≤ M → HasPlanarDrawingOn M → M = N := by sorry
