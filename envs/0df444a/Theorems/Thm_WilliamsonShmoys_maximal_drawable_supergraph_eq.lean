-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_eq
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:17:33.51715+00:00
-- url     : https://prove2.me/theorems/583b06de-b800-438c-a66d-0226ac3291f6
-- title:
--   A drawable supergraph of a maximal drawable graph is equal to it
-- statement:
--   If a drawable graph has no drawable proper edge-supergraph, then every drawable graph containing it on the same vertices is equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_eq
    {V : Type} [Fintype V] [LinearOrder V]
    (L K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet → ¬ HasPlanarDrawingOn M)
    (hLK : L ≤ K)
    (hKDraw : HasPlanarDrawingOn K) :
    L = K := by sorry
