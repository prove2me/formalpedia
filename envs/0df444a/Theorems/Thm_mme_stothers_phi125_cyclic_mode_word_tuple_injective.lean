-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_mode_word_tuple_injective
-- name    : mme_stothers_phi125_cyclic_mode_word_tuple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:24:53.672901+00:00
-- url     : https://prove2.me/theorems/2adff2be-2446-4cbf-baa9-737387750023
-- title:
--   The three cyclic phi_125 vertices determine the edge
-- statement:
--   For α+β+γ=N, the ordered triple of cyclic mode vertices uniquely determines a cyclic exact φ₁₂₅ edge. Indeed, the three vertices expose every mode word of every exact-profile copy, and the six supported φ₁₂₅ grade patterns are distinct. This converts distinct edges into a distinct cyclic mode code for the pair-collision estimate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), exact φ₁₂₅ support and type-2 hash in Lemma 5.1(ii); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_mode_word_tuple_injective
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Function.Injective
      (fun e : MME.StothersFourth.Phi125.CyclicExactEdge
          N alpha beta gamma ↦
        MME.StothersFourth.Phi125.cyclicModeWord e) := by
  sorry
