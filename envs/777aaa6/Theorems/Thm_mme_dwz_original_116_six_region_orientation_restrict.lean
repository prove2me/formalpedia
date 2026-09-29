-- Prove2me | Theorems.Thm_mme_dwz_original_116_six_region_orientation_restrict
-- name    : mme_dwz_original_116_six_region_orientation_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:00:27.04362+00:00
-- url     : https://prove2.me/theorems/36397406-a605-4225-aab9-a3045231d9a9
-- title:
--   Original T116 six-region orientation preserves the prescribed parent profile
-- statement:
--   For any three tensors $A_0,A_1,A_2$ over a field, let $\rho$ be the cyclic mode permutation and $\sigma$ the swap of the first two modes. Set $B_r=\rho^r A_r$ and
--   $$
--   S=\bigotimes_{r=0}^2(B_r\otimes\sigma B_r).
--   $$
--   Writing $\operatorname{cyc}$ and $\operatorname{sym}_6$ for cyclic and six-fold symmetrization, respectively, there is a tensor isomorphism
--   $$
--   \operatorname{cyc}(S)\cong\operatorname{sym}_6\!\left(\bigotimes_{r=0}^2 A_r\right).
--   $$
--   The isomorphism is a genuine mutual linear restriction, not an equality of scalar value estimates.
--
--   For the actual fourth-power constituent $T_{1,1,6}$ of $\mathrm{CW}_q$, take $A_r$ to be its prescribed-Z regional power with the exact regional profile and integer multiplicity in the published original-116 regional data. The cyclic symmetrization of $S$ restricts from the six-fold symmetrization of the ORIGINAL prescribed-Z power of $T_{1,1,6}$. This holds for every field, every $q$, and every permitted integer scale $m$, including $q=5$ and $q=6$.
--
--   Crucially, the mode rotations are applied to the already projected tensor objects. They therefore transport the original Z filter to the appropriate mode instead of imposing a new Z filter after rotation. The original parent and all regional profiles remain unchanged. This establishes the finite orientation and assembly in DWZ Claims 7.2–7.3; it does not assert child extraction, a positive-component value, or an exponent bound.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5#S7, Claims 7.2 and 7.3. Exact original-T116 specialization of the regional profile data; generic isomorphism independent of q.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_dwz_positive_116_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_CW_2376_address_block

open MME MME.TensorObj MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent116
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_original_116_six_region_orientation_restrict {K : Type u} [Field K] :
    (∀ A : Fin 3 → TensorObj K 3,
      let B : Fin 3 → TensorObj K 3 := ![A 0, permObj cyclicPerm (A 1),
        permObj (cyclicPerm.trans cyclicPerm) (A 2)]
      TensorObj.Isomorphic
        (cyclicSymmetrization (kronFin 3 (fun r ↦
          kron (B r) (permObj swapFirstTwoPerm (B r)))))
        (sixSymmetrization (kronFin 3 A))) ∧
    ∀ q m : ℕ,
      let A := fun r : Fin 3 ↦ prescribedZPower
        (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
        (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)
      let B : Fin 3 → TensorObj K 3 := ![A 0, permObj cyclicPerm (A 1),
        permObj (cyclicPerm.trans cyclicPerm) (A 2)]
      TensorObj.Restrict
        (cyclicSymmetrization (kronFin 3 (fun r ↦
          kron (B r) (permObj swapFirstTwoPerm (B r)))))
        (sixSymmetrization (prescribedZPower
          (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
          (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
          parentProfile m)) := by sorry
