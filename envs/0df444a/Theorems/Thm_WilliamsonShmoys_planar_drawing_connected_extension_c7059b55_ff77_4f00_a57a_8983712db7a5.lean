-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_c7059b55_ff77_4f00_a57a_8983712db7a5
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_c7059b55_ff77_4f00_a57a_8983712db7a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:50:15.719041+00:00
-- url     : https://prove2.me/theorems/ae93abfd-b481-400c-bbb6-90694b999a88
-- title:
--   Connected planar supergraph extension
-- statement:
--   A drawn simple graph on at least three vertices has a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_c7059b55_ff77_4f00_a57a_8983712db7a5
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N := by sorry
