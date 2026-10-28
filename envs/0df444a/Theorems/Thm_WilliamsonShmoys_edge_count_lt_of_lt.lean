-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_lt_of_lt
-- name    : WilliamsonShmoys.edge_count_lt_of_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:12:32.359555+00:00
-- url     : https://prove2.me/theorems/bebabb54-0b78-4f43-a01c-cc64a8878a3b
-- title:
--   Strict graph inclusion increases finite edge count
-- statement:
--   If K is a strict subgraph of L on a finite vertex type, then K has strictly fewer edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_lt_of_lt {V : Type} [Fintype V] [LinearOrder V] (K L : SimpleGraph V) (h : K < L) : Nat.card {e : Sym2 V // e ∈ K.edgeSet} < Nat.card {e : Sym2 V // e ∈ L.edgeSet} := by sorry
