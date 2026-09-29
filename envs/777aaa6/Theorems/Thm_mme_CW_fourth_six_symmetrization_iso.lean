-- Prove2me | Theorems.Thm_mme_CW_fourth_six_symmetrization_iso
-- name    : mme_CW_fourth_six_symmetrization_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:56:42.508803+00:00
-- url     : https://prove2.me/theorems/bb2ca6c2-09dc-43b8-87ad-bf7f84e15c53
-- title:
--   The full symmetrization of the fourth CW tensor is its sixth power
-- statement:
--   Let $K$ be any field and let $q$ be a nonnegative integer. For the literal fourth CW tensor $T=CW_q^{\otimes4}$, the full sixfold symmetrization obeys
--   $$
--   \operatorname{sym}_6(T)\simeq T^{\otimes6}.
--   $$
--   Here $\operatorname{sym}_6$ is the product over all six permutations of the tensor modes, in the existing public parenthesization. This equivalence converts the six-symmetrized value normalization in DWZ into ordinary tensor-power value semantics for the actual fourth-power source.
--
--   **Formalization Note** The public predicate Isomorphic records tensor restrictions in both directions. The statement is uniform in $q$, including $q=5$, and makes no value lower-bound assertion.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Definition 3.3, printed p. 18 (sixfold symmetrized value), and Section 3.4 (symmetric CW tensor); https://arxiv.org/abs/2210.10173. This fourth-power adapter follows from the existing CW-square sixfold symmetry and symmetrization/power compatibility.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_tensor_quotient

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_six_symmetrization_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization (MME.StothersFourth.cwFourthObj K q))
      ((MME.StothersFourth.cwFourthObj K q).kronPow 6) := by
  sorry
