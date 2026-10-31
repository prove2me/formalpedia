-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
-- name    : WilliamsonShmoys.planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:19.535692+00:00
-- url     : https://prove2.me/theorems/ecabda78-d401-4f6a-900f-746421d84865
-- title:
--   Connect a disconnected drawable graph by a drawable supergraph
-- statement:
--   Every disconnected finite drawable graph on at least three vertices has a connected drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
