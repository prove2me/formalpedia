-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_identity_of_connected
-- name    : WilliamsonShmoys.maximal_drawing_euler_identity_of_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:28:20.249521+00:00
-- url     : https://prove2.me/theorems/e8633538-2938-47c7-9d02-dfc0ca9506b9
-- title:
--   Edge-count identity for a connected maximal drawable graph
-- statement:
--   For a connected finite simple graph with a crossing-free drawing, maximality under drawable edge additions and at least three vertices imply the planar edge-count identity. A proof route is to formalize faces of the given drawing, show maximality forces every face boundary to have length three, and combine the face-edge incidence count with Euler’s formula. The connectedness child lets this argument assume one component; this child preserves the original quantitative conclusion and isolates the remaining topological work. The three-vertex case must be included in the face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_euler_identity_of_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hConnected : K.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
