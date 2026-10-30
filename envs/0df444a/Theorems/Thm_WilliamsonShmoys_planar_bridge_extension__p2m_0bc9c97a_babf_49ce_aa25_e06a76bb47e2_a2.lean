-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- name    : WilliamsonShmoys.planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:58.999959+00:00
-- url     : https://prove2.me/theorems/5b011f3a-cb0c-4217-84d6-286f15b556e3
-- title:
--   Extend a planar drawing across disconnected components
-- statement:
--   If two distinct vertices of a planar drawing lie in different connected components, there is a strictly larger planar supergraph on the same vertices. Prove this by adding an edge drawn through the complement and checking the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (u v : V) (huv : Not (u = v)) (hnotreach : Not (G.Reachable u v)) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (Not (G = K)) (HasPlanarDrawingOn K)) := by sorry
