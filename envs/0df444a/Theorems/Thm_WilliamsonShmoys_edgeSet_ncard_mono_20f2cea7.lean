-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_20f2cea7
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_20f2cea7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:56:59.992494+00:00
-- url     : https://prove2.me/theorems/39fbeff9-37c7-4942-ac31-7682392210b8
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For graphs on a finite vertex type, inclusion implies monotonicity of the cardinality of their edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeSet_ncard_mono_20f2cea7
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
