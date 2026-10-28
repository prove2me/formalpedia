-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_b426a2d2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_b426a2d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:32:56.735276+00:00
-- url     : https://prove2.me/theorems/1fe1f07f-07ec-4776-a7f0-59fdee2ec340
-- title:
--   A planar graph has an inclusion-maximal planar supergraph
-- statement:
--   Any graph with such a drawing on a finite vertex type has a supergraph on the same vertices that is maximal among graphs with such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

-- A finite maximality argument: simple graphs on V form a finite set; maximize edge-set cardinality among the planar supergraphs of G. The drawing predicate and inclusion hypotheses are preserved by the selected family.

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_b426a2d2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        ∀ H : SimpleGraph V, U ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U := by sorry
