-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
-- name    : mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:45:39.523102+00:00
-- url     : https://prove2.me/theorems/c5812da9-7bd7-4aaf-8e0e-8e9f24ae98a9
-- title:
--   The exact phi_134 cyclic component product restricts to its literal address block
-- statement:
--   Fix an exact cyclic $\Phi_{1,3,4}$ edge, consisting of three addresses with the prescribed eight-entry joint profile. Let $P$ be the product containing each of the eight source-faithful component tensors with its prescribed multiplicity. Then the cyclic symmetrization of $P$ restricts to the literal graded address block attached to the edge: $$ \operatorname{cyc}(P) \le_{\mathrm{res}} B_e. $$ This identifies the common algebraic payload carried by every retained exact-profile edge and is the interface that converts retained-edge cardinality into weighted matrix-multiplication volume.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the eight phi_134 factors and their cyclic product in Lemma 5.1(iii), p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_cyclic_triple_grading
import Definitions.Def_mme_stothers_phi134_cyclic_grading_address
import Definitions.Def_mme_stothers_phi134_outer_grading

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (e : MME.StothersFourth.Phi134.CyclicExactEdge
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 8 (fun r ↦
          (MME.StothersFourth.Phi134.componentObj K q r).kronPow
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r))))
      (gradedAddressBlock
        (mmeCyclicTripleGrading
          (MME.StothersFourth.Phi134.outerGrading K q))
        (MME.StothersFourth.Phi134.cyclicGradingAddress e)) := by
  sorry
