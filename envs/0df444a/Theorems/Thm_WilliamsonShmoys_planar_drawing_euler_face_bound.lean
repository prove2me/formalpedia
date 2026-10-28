-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_bound
-- name    : WilliamsonShmoys.planar_drawing_euler_face_bound
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T22:17:12.871677+00:00
-- url     : https://prove2.me/theorems/fd0a772c-e1ff-4a64-a9cb-f5764bf93bc4
-- title:
--   Face bound from planar edge density and Euler’s relation
-- statement:
--   For a simple graph with a crossing-free drawing, at least three vertices, and at least two edges, any face and component counts satisfying Euler’s relation obey the aggregate face-degree bound. Using Euler’s equation, this is the component-sensitive planar edge bound; it can be proved by applying planar edge density to nontrivial components and handling isolated vertices and small components separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard)
    (f c : ℕ)
    (heuler : Fintype.card V + f = L.edgeSet.ncard + c + 1) :
    3 * f ≤ 2 * L.edgeSet.ncard := by sorry
