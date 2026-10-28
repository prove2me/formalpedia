-- Prove2me | Theorems.Thm_WilliamsonShmoys_single_edge_extension_has_strict_edgeSet
-- name    : WilliamsonShmoys.single_edge_extension_has_strict_edgeSet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:21:55.873659+00:00
-- url     : https://prove2.me/theorems/a7691049-bf9e-4fed-9afa-fc66803a92e3
-- title:
--   Adding a missing bridge strictly enlarges the edge set
-- statement:
--   If L has exactly the edges of K together with the edge between unreachable vertices u and v, then K's edge set is a proper subset of L's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.single_edge_extension_has_strict_edgeSet
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (u v : V)
    (hUV : ¬ K.Reachable u v)
    (hAdj : ∀ a b, L.Adj a b ↔ K.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    K.edgeSet ⊂ L.edgeSet := by sorry
