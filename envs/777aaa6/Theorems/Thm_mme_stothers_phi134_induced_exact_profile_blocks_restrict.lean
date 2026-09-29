-- Prove2me | Theorems.Thm_mme_stothers_phi134_induced_exact_profile_blocks_restrict
-- name    : mme_stothers_phi134_induced_exact_profile_blocks_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:44:56.91768+00:00
-- url     : https://prove2.me/theorems/645fe8ee-c51d-4213-995f-65b8b16ab409
-- title:
--   An induced Phi_134 exact-profile family realizes disjoint literal blocks
-- statement:
--   Fix a finite family $E$ of cyclic exact-profile edges for $\Phi_{1,3,4}$. Assume it is induced: whenever three members of $E$ can be mixed modewise without leaving the eight supported outer types, all three members coincide. If $P$ is the common eight-component tensor product determined by the profile, then
--
--   $$
--   \bigoplus_{e\in E} \operatorname{cyc}(P)\;\leq_{\mathrm{res}}\;\operatorname{cyc}(\Phi_{1,3,4})^{\otimes 2N}.
--   $$
--
--   This turns the combinatorial induced-family certificate produced by affine hashing into a literal tensor restriction. Each retained edge contributes one independent copy of the same exact-profile algebraic payload.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(iii), pp. 359--365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME BigOperators
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_induced_exact_profile_blocks_restrict
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (kept : Finset (MME.StothersFourth.Phi134.CyclicExactEdge
      N alpha beta gamma delta))
    (hdiag : ∀ x y z : kept,
      MME.StothersFourth.Phi134.CyclicCoordinatewiseSupported x.1 y.1 z.1 →
        x = y ∧ y = z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization
          (TensorObj.kronFin 8 (fun r ↦
            (MME.StothersFourth.Phi134.componentObj K 6 r).kronPow
              (MME.StothersFourth.Phi134.profileMultiplicity
                alpha beta gamma delta r)))))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
          (2 * N)) := by
  sorry
