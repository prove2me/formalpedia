-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block
-- name    : mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:55:35.938905+00:00
-- url     : https://prove2.me/theorems/6a24de52-230c-4a82-8403-16f5b8060028
-- title:
--   The exact $\Phi_{233}$ cyclic component product restricts to its literal address block
-- statement:
--   Fix an exact cyclic $\Phi_{233}$ edge, consisting of three addresses with the prescribed ten-entry joint profile. Let $P$ be the product containing each of the ten source-faithful component tensors with its prescribed multiplicity. Then the cyclic symmetrization of $P$ restricts to the literal graded address block attached to the edge:
--
--   $$
--   \operatorname{cyc}(P) \le_{\mathrm{res}} B_e.
--   $$
--
--   This identifies the common algebraic payload carried by every retained exact-profile edge. It combines the previously proved ten-component restriction atlas with the cyclic word-block factorization, and is the interface needed to convert retained-edge cardinality into weighted matrix-multiplication volume.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the ten phi_233 factors and their cyclic product in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_cyclic_grading_address_block_iso
import Theorems.Thm_mme_stothers_phi233_exact_component_product_restrict_outer_address_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (e : MME.StothersFourth.Phi233.CyclicExactEdge
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 10 (fun r ↦
          (MME.StothersFourth.Phi233.componentObj K q r).kronPow
            (MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r))))
      (gradedAddressBlock
        (mmeCyclicTripleGrading
          (MME.StothersFourth.Phi233.outerGrading K q))
        (MME.StothersFourth.Phi233.cyclicGradingAddress
          (MME.StothersFourth.Phi233.exactToAmbient e))) := by
  sorry
