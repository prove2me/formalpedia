-- Prove2me | Theorems.Thm_MME_StothersFourth_fixedHash_retained_vertex_closed
-- name    : MME.StothersFourth.fixedHash_retained_vertex_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:49:28.605482+00:00
-- url     : https://prove2.me/theorems/7f5a5364-6436-496e-b7a2-aae5ed965eb7
-- title:
--   Vertex closure of the fixed Stothers affine-hash family
-- statement:
--   Let $S$ be a three-term-progression-free subset of the lower half of an odd modulus. The marginally regular addresses retained by the three fixed Stothers affine hashes form a vertex-closed family: whenever three retained addresses can be mixed coordinatewise into a supported address, that mixed address is itself retained. The grade-sum-eight identity makes the three hash labels an arithmetic progression, so progression-freeness forces a common label.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.fixedHash_retained_vertex_closed
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (MME.StothersFourth.fixedOuterLength m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    MME.StothersFourth.FixedMarginalVertexClosed
      (MME.StothersFourth.fixedHashRetainedEdges m p S b0 w) := by
  sorry
