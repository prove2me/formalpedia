-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_2d69255633d74159
-- name    : WilliamsonShmoys.planar_completion_maximal_2d69255633d74159
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:47:19.359289+00:00
-- url     : https://prove2.me/theorems/0f2415c4-9a6b-404e-942c-8828a359d5d0
-- title:
--   Existence of a maximal planar completion
-- statement:
--   Every finite planar graph on V is contained in a planar graph maximal by edge inclusion among planar supergraphs on V. Since there are finitely many simple graphs on V and G itself is eligible, choose an eligible graph with maximal edge-set cardinality. Any planar supergraph of it must then have the same edge set. The drawing predicate is preserved as an existence witness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_maximal_2d69255633d74159
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet ⊆ P.edgeSet := by sorry
