-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_maximal_f2db904c_5721_454a_bbac_7987a5a61819
-- name    : WilliamsonShmoys.planar_drawing_extension_to_maximal_f2db904c_5721_454a_bbac_7987a5a61819
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:43:47.912638+00:00
-- url     : https://prove2.me/theorems/56ca1009-81ee-463f-8c6c-b19a5964c150
-- title:
--   Extend a connected drawable graph to a maximal drawable supergraph
-- statement:
--   Extend the input graph on the same finite vertex type to a drawable graph maximal among its drawable supergraphs. The extension stays connected because it contains the connected input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extension_to_maximal_f2db904c_5721_454a_bbac_7987a5a61819
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hQconn : Q.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.Connected ∧
      ∀ S : SimpleGraph V,
        R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by sorry
