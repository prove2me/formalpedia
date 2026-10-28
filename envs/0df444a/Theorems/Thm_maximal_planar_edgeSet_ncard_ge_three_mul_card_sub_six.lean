-- Prove2me | Theorems.Thm_maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six
-- name    : maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:46:35.610118+00:00
-- url     : https://prove2.me/theorems/e934ca93-253c-4194-a800-c4803b62778f
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A graph with the supplied drawing that admits no strictly larger planar supergraph on the same vertex type has at least 3|V|−6 edges. A proof route shows maximality forces connectivity and triangular faces, then uses Euler's formula and the face-degree count. The lower-bound direction retains the same vertex-count hypothesis, so the subtraction cutoff is handled by the parent arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : forall L : SimpleGraph V, G <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = G)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by sorry
