-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connectivity_completion
-- name    : WilliamsonShmoys.planar_connectivity_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:38:10.908773+00:00
-- url     : https://prove2.me/theorems/085be6a9-0970-468f-8c62-5139d0d2aa22
-- title:
--   Connected planar completion of a drawn graph
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing can be augmented on the same vertices to a connected graph with a crossing-free drawing, without losing any edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connectivity_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.Connected ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
