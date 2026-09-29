-- Prove2me | Definitions.Def_mme_stothers_phi134_profile_data
-- name    : mme_stothers_phi134_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T09:10:21.295906+00:00
-- url     : https://prove2.me/theorems/a8ca9866-75dc-4940-b4ca-a8876f34a13b
-- title:
--   Exact and marginal finite profiles for the phi_134 extraction
-- statement:
--   The eight summands of the Davie–Stothers constituent phi_134 are indexed in the source order (004), (013), (022), (031), (103), (112), (121), (130). For alpha+beta+gamma+delta=N, its symmetric length-2N profile has multiplicities (alpha,beta,gamma,delta,delta,gamma,beta,alpha), with the three marginal histograms printed in Lemma 5.1(iii). This definition records exact profiles, the marginal completion family, the literal fourth-power fine blocks, and their source-faithful algebraic payloads. It is the common finite interface for the phi_134 hashing and tensor-realization proof.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge

open MME BigOperators

universe u

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

def ProfileAddress (N : ℕ) : Type := Fin 3 → Fin (2 * N) → Fin 5

def pattern : Fin 8 → Fin 3 → Fin 5 := ![cwSquareBlockType 0 0 4, cwSquareBlockType 0 1 3, cwSquareBlockType 0 2 2, cwSquareBlockType 0 3 1, cwSquareBlockType 1 0 3, cwSquareBlockType 1 1 2, cwSquareBlockType 1 2 1, cwSquareBlockType 1 3 0]

def addressType {N : ℕ} (x : ProfileAddress N) (j : Fin (2 * N)) : Fin 3 → Fin 5 := fun i ↦ x i j

def profileMultiplicity (alpha beta gamma delta : ℕ) : Fin 8 → ℕ := ![alpha, beta, gamma, delta, delta, gamma, beta, alpha]

def marginalMultiplicity (N alpha beta gamma delta : ℕ) : Fin 3 → Fin 5 → ℕ := ![![N, N, 0, 0, 0], ![alpha + delta, beta + gamma, beta + gamma, alpha + delta, 0], ![alpha, beta + delta, 2 * gamma, beta + delta, alpha]]

def CoordinatewiseSupported {N : ℕ} (x : ProfileAddress N) : Prop := ∀ j, ∃ r : Fin 8, addressType x j = pattern r

def MarginalAddress (N alpha beta gamma delta : ℕ) : Type := {x : ProfileAddress N // CoordinatewiseSupported x ∧ ∀ i : Fin 3, ∀ k : Fin 5, ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦ x i j = k)).card = marginalMultiplicity N alpha beta gamma delta i k}

def ExactProfileAddress (N alpha beta gamma delta : ℕ) : Type := {x : MarginalAddress N alpha beta gamma delta // ∀ r : Fin 8, ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦ addressType (Subtype.val x) j = pattern r)).card = profileMultiplicity alpha beta gamma delta r}

noncomputable def fineSourceObj (K : Type u) [Field K] (q : ℕ) : Fin 8 → TensorObj K 3 := ![Phi116.cwFourthFineBlockObj K q 0 0 4 1 3 0, Phi116.cwFourthFineBlockObj K q 0 1 3 1 2 1, Phi116.cwFourthFineBlockObj K q 0 2 2 1 1 2, Phi116.cwFourthFineBlockObj K q 0 3 1 1 0 3, Phi116.cwFourthFineBlockObj K q 1 0 3 0 3 1, Phi116.cwFourthFineBlockObj K q 1 1 2 0 2 2, Phi116.cwFourthFineBlockObj K q 1 2 1 0 1 3, Phi116.cwFourthFineBlockObj K q 1 3 0 0 0 4]

noncomputable def componentObj (K : Type u) [Field K] (q : ℕ) : Fin 8 → TensorObj K 3 := ![MMObj K 1 (2 * q) 1, TensorObj.kron (MMObj K 1 1 (2 * q)) (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)), TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2)) (coupledObj K q), MMObj K (2 * q) 1 (2 * q), MMObj K (2 * q) 1 (2 * q), TensorObj.kron (coupledObj K q) (MMObj K 1 1 (q ^ 2 + 2)), TensorObj.kron (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)) (MMObj K 1 1 (2 * q)), MMObj K 1 (2 * q) 1]

end MME.StothersFourth.Phi134


