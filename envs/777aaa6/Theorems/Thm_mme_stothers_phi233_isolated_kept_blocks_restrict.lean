-- Prove2me | Theorems.Thm_mme_stothers_phi233_isolated_kept_blocks_restrict
-- name    : mme_stothers_phi233_isolated_kept_blocks_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:02:16.68209+00:00
-- url     : https://prove2.me/theorems/49ed8f13-1c6a-4b88-9030-5882d5f40973
-- title:
--   An isolated $\Phi_{233}$ cyclic family gives an induced direct-sum restriction
-- statement:
--   Let $E_0$ be the exact-profile cyclic $\Phi_{233}$ family and let $E$ be its full same-marginal completion family. Suppose a finite retained family $E'\subseteq E_0$ has two properties: each of its three vertex projections is injective, and any ambient edge whose three vertices occur in $E'$ already belongs to $E'$. Then $E'$ is an induced matching with respect to the literal tensor support, and the direct sum of its graded address blocks restricts from the $(2N)$-th power of the cyclic symmetrization:
--
--   $$
--   \bigoplus_{e\in E'} B_e\;\le_{\mathrm{res}}\;
--   \operatorname{cyc}(\Phi_{233})^{\otimes 2N}.
--   $$
--
--   This theorem is the exact tensor-realization endpoint consumed by the affine hashing argument. It separates the algebraic support proof from the finite-field estimates used to construct a large isolated retained family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and the exceptional phi_233 construction in Lemma 5.1(v), pp. 356--360 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_induced_word_zeroing
import Theorems.Thm_mme_type2_ambient_isolated_induced_and_blocks_restrict
import Theorems.Thm_mme_stothers_phi233_cyclic_target_ambient_closure
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_stothers_phi233_outer_grading_support

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_isolated_kept_blocks_restrict
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (kept : Finset
      (MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta))
    (hkept : kept ⊆
      MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta)
    (hisolated :
      ∀ e ∈ MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta,
        (∀ i : Fin 3, ∃ f ∈ kept,
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord f i) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦
        MME.StothersFourth.Phi233.cyclicModeWord e.1 i)) :
    (∀ x y z : kept,
      MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
          x.1 y.1 z.1 →
        x = y ∧ y = z) ∧
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock
          (mmeCyclicTripleGrading
            (MME.StothersFourth.Phi233.outerGrading K q))
          (MME.StothersFourth.Phi233.cyclicGradingAddress
            (kept.equivFin.symm j).1)))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) := by
  sorry
