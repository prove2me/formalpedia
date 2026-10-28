-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:41:19.489977+00:00
-- url     : https://prove2.me/theorems/d06bc7a8-4fcc-473b-a9a0-67baa3c88c78
-- title:
--   Every drawn planar graph has a maximal planar supergraph
-- statement:
--   Any finite graph with a planar drawing is contained, on the same vertex set, in a planar graph maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧ L.edgeSet ⊆ M.edgeSet ∧ ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet := by sorry
