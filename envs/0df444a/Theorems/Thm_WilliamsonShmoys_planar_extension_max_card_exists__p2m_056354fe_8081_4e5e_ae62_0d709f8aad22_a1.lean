-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- name    : WilliamsonShmoys.planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:56.377477+00:00
-- url     : https://prove2.me/theorems/c9ac7080-e35c-4e9a-9a08-f24b850d3d66
-- title:
--   Maximum-cardinality planar extension exists
-- statement:
--   Among the planar supergraphs of a given planar graph on a finite ordered vertex type, one has maximum ordered-adjacency cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → Nat.card {p : V × V // L.Adj p.1 p.2} ≤ Nat.card {p : V × V // K.Adj p.1 p.2} := by sorry
