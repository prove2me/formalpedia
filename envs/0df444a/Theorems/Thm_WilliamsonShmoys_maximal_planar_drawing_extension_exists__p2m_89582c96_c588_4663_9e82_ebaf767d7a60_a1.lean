-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:07.726939+00:00
-- url     : https://prove2.me/theorems/55be6006-4b21-4039-be32-5973123fa254
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type. The proof route is to choose, from the finite collection of supergraphs of K that have drawings, one with the largest edge set. Any drawable supergraph of that choice must then have the same edges. This isolates the finite maximization step from the geometric edge-count argument; the hypothesis |V| ≥ 3 is preserved for composition with the next child, though maximality itself does not require it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
