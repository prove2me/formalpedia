-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connected_extension
-- name    : WilliamsonShmoys.planarDrawingOn_connected_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:21:11.884036+00:00
-- url     : https://prove2.me/theorems/e94ffa9f-3e6d-4dc4-89d5-b73f094dba37
-- title:
--   Connected spanning extension of a planar drawing
-- statement:
--   A finite drawable graph with at least three vertices has a connected drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_connected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V => J <= K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
