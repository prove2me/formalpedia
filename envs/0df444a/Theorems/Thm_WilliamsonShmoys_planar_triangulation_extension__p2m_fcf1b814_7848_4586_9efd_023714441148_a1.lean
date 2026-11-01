-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:31:28.381081+00:00
-- url     : https://prove2.me/theorems/59f689b9-056b-46e8-a00d-961751c5f3da
-- title:
--   Triangulated planar extension on the same vertices
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge set contains the original edge set and has exactly 3|V|−6 edges. This is the classical extension to a maximal planar triangulation, expressed using the project’s drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
