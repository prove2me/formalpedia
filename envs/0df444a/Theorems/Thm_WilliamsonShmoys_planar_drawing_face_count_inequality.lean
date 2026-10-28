-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_inequality
-- name    : WilliamsonShmoys.planar_drawing_face_count_inequality
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:37:07.267066+00:00
-- url     : https://prove2.me/theorems/2c2efb55-c875-4804-83b1-0ac0a059f6e4
-- title:
--   Euler face data from a connected planar drawing
-- statement:
--   For the supplied crossing-free drawing of a connected simple graph with at least three vertices, there is a finite face type whose cardinality satisfies Euler’s equation, and whose face incidences imply that three times the number of faces is at most twice the number of edges. This removes the geometric embedding and face-counting work from the parent; the parent then closes by linear arithmetic. A proof route is to extract cyclic neighbor orders and face walks from the arcs, use the connected plane graph Euler formula, and count each edge’s two dart incidences while showing each face walk has length at least three. The remaining core obligation is this topological extraction and verification from `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_inequality {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ (F : Type) (inst : Fintype F), @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧ 3 * @Fintype.card F inst ≤ 2 * H.edgeSet.ncard := by sorry
