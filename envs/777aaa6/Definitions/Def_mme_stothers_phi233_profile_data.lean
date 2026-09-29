-- Prove2me | Definitions.Def_mme_stothers_phi233_profile_data
-- name    : mme_stothers_phi233_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T21:30:30.728514+00:00
-- url     : https://prove2.me/theorems/d568cf8c-f5c0-47fc-9907-49b7fe1cb169
-- title:
--   Exact type-2 profile data for the phi_233 constituent
-- statement:
--   This module records the exact finite data used in the $\varphi_{233}$ case of Davie--Stothers Lemma 5.1(v). A length-$2N$ address uses the ten ordered square-pair types $$013,022,031,103,112,121,130,202,211,220$$ with joint multiplicities $$(\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).$$ It defines both the target exact-profile family $S_0$ and the larger family $S$ of all supported addresses having the same three marginals. It also records the ten literal fine fourth-power blocks and the corresponding restricted algebraic payloads from the component atlas. These data make the nontrivial completion family explicit rather than assuming it is a singleton.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 setup and Equation (3.6), pp. 359--360, and Lemma 5.1(v), p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge

open MME

universe u

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- A three-mode word of first-square grades in a `phi_233` tensor power. -/
def ProfileAddress (N : ℕ) : Type :=
  Fin 3 → Fin (2 * N) → Fin 5

/-- The ten ordered square-pair types in the exact source order
`013,022,031,103,112,121,130,202,211,220`. -/
def pattern : Fin 10 → Fin 3 → Fin 5 :=
  ![cwSquareBlockType 0 1 3,
    cwSquareBlockType 0 2 2,
    cwSquareBlockType 0 3 1,
    cwSquareBlockType 1 0 3,
    cwSquareBlockType 1 1 2,
    cwSquareBlockType 1 2 1,
    cwSquareBlockType 1 3 0,
    cwSquareBlockType 2 0 2,
    cwSquareBlockType 2 1 1,
    cwSquareBlockType 2 2 0]

/-- Joint type at one tensor-power coordinate. -/
def addressType {N : ℕ} (x : ProfileAddress N) (j : Fin (2 * N)) :
    Fin 3 → Fin 5 :=
  fun i ↦ x i j

/-- The source profile
`(alpha,beta,alpha,gamma,delta,delta,gamma,alpha,beta,alpha)`. -/
def profileMultiplicity
    (alpha beta gamma delta : ℕ) : Fin 10 → ℕ :=
  ![alpha, beta, alpha, gamma, delta,
    delta, gamma, alpha, beta, alpha]

/-- The three mode marginals printed in Lemma 5.1(v). -/
def marginalMultiplicity
    (alpha beta gamma delta : ℕ) : Fin 3 → Fin 5 → ℕ :=
  ![![2 * alpha + beta, 2 * gamma + 2 * delta,
        2 * alpha + beta, 0, 0],
    ![alpha + gamma, alpha + beta + delta,
        alpha + beta + delta, alpha + gamma, 0],
    ![alpha + gamma, alpha + beta + delta,
        alpha + beta + delta, alpha + gamma, 0]]

/-- Coordinatewise support in the ten fine blocks of `phi_233`. -/
def CoordinatewiseSupported {N : ℕ} (x : ProfileAddress N) : Prop :=
  ∀ j, ∃ r : Fin 10, addressType x j = pattern r

/-- The full same-marginal completion family `S` in the type-2 analysis. -/
def MarginalAddress
    (N alpha beta gamma delta : ℕ) : Type :=
  {x : ProfileAddress N //
    CoordinatewiseSupported x ∧
      ∀ i : Fin 3, ∀ k : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ x i j = k)).card =
            marginalMultiplicity alpha beta gamma delta i k}

/-- The target exact-profile family `S₀`, as a subtype of its full
same-marginal completion family. -/
def ExactProfileAddress
    (N alpha beta gamma delta : ℕ) : Type :=
  {x : MarginalAddress N alpha beta gamma delta //
    ∀ r : Fin 10,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ addressType (Subtype.val x) j = pattern r)).card =
          profileMultiplicity alpha beta gamma delta r}

/-- Literal fine fourth-power blocks indexed in the same order as `pattern`. -/
noncomputable def fineSourceObj
    (K : Type u) [Field K] (q : ℕ) : Fin 10 → TensorObj K 3 :=
  ![Phi116.cwFourthFineBlockObj K q 0 1 3 2 2 0,
    Phi116.cwFourthFineBlockObj K q 0 2 2 2 1 1,
    Phi116.cwFourthFineBlockObj K q 0 3 1 2 0 2,
    Phi116.cwFourthFineBlockObj K q 1 0 3 1 3 0,
    Phi116.cwFourthFineBlockObj K q 1 1 2 1 2 1,
    Phi116.cwFourthFineBlockObj K q 1 2 1 1 1 2,
    Phi116.cwFourthFineBlockObj K q 1 3 0 1 0 3,
    Phi116.cwFourthFineBlockObj K q 2 0 2 0 3 1,
    Phi116.cwFourthFineBlockObj K q 2 1 1 0 2 2,
    Phi116.cwFourthFineBlockObj K q 2 2 0 0 1 3]

/-- Source-faithful algebraic payloads supplied by the ten-block restriction
atlas. -/
noncomputable def componentObj
    (K : Type u) [Field K] (q : ℕ) : Fin 10 → TensorObj K 3 :=
  ![MMObj K 1 (q ^ 2 + 2) (2 * q),
    TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2))
      (TensorObj.permObj cyclicPerm (coupledObj K q)),
    MMObj K (q ^ 2 + 2) 1 (2 * q),
    MMObj K (2 * q) (2 * q) 1,
    TensorObj.kron (coupledObj K q)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)),
    TensorObj.kron
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (coupledObj K q),
    MMObj K (2 * q) (2 * q) 1,
    MMObj K (q ^ 2 + 2) 1 (2 * q),
    TensorObj.kron (TensorObj.permObj cyclicPerm (coupledObj K q))
      (MMObj K 1 1 (q ^ 2 + 2)),
    MMObj K 1 (q ^ 2 + 2) (2 * q)]

end MME.StothersFourth.Phi233


