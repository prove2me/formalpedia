-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion_eb48bd77
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_completion_eb48bd77
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:41:51.777203+00:00
-- url     : https://prove2.me/theorems/93e3f93a-106a-4e19-a831-d28109b1d9b8
-- title:
--   Existence of an edge-maximal drawable completion
-- statement:
--   Every drawable graph on the given finite ordered vertex type is contained in a drawable graph with no drawable proper supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_completion_eb48bd77
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      N.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet → ¬ HasPlanarDrawingOn M := by sorry
