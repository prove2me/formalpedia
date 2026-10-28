-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_supergraph
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:17:38.006814+00:00
-- url     : https://prove2.me/theorems/c50528b3-1180-4c07-8542-83a5279d07ed
-- title:
--   Finite maximality for simple graph extensions
-- statement:
--   For any property of simple graphs on a finite ordered vertex type, if the starting graph has the property, there is a property-satisfying supergraph that has no strictly larger property-satisfying supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_simpleGraph_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop) (hQ : Q G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ Q K ∧
      ∀ L : SimpleGraph V, K ≤ L → Q L → L = K := by sorry
