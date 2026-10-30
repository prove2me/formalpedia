-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- name    : WilliamsonShmoys.exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:42.838523+00:00
-- url     : https://prove2.me/theorems/732ef142-c02d-434e-9b88-adbee85d4bda
-- title:
--   A planar supergraph with maximum edge cardinality
-- statement:
--   Among drawable supergraphs of K on the same finite vertex type, there is one whose finite edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → Nat.card {e : Sym2 V // e ∈ M.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ L.edgeSet} := by sorry
