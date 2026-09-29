-- Prove2me | solution 1 for mme_stothers_phi134_finite_power_block_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:45:42.669381+00:00
-- url     : https://prove2.me/submissions/5435df48-1a8d-4be9-9cc6-c31736792b13

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_stothers_phi134_exact_profile_product_cyclic_value_below
import Theorems.Thm_mme_stothers_phi134_induced_exact_profile_blocks_restrict
import Theorems.Thm_mme_stothers_phi134_weighted_isolated_profile_family

open MME BigOperators
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 300000

theorem solution
    {K : Type u} [Field K] (tau sigma a c : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((MME.StothersFourth.L 6 tau / sigma) ^ sigma *
            (MME.StothersFourth.E 6 tau / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((MME.StothersFourth.H 6 tau / 2) / c) ^ c *
            (MME.StothersFourth.E 6 tau / (1 - a - c)) ^
              (1 - a - c))) :
    ∃ (N alpha beta gamma delta : ℕ),
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ (kept : Finset
          (CyclicExactEdge N alpha beta gamma delta))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  classical
  let L := MME.StothersFourth.L 6 tau
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  have hL : 0 < L := by
    unfold L MME.StothersFourth.L
    positivity
  have hE : 0 < E := by
    unfold E MME.StothersFourth.E
    positivity
  have hH : 0 < H := by
    unfold H MME.StothersFourth.H
    positivity
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum,
      kept, hmode, hdiag, hweighted⟩ :=
    mme_stothers_phi134_weighted_isolated_profile_family
      sigma a c L E H V ha hc hcs hsa hL hE hH hV (by
        simpa only [L, E, H] using hVlt)
  let B : ℝ :=
    L ^ (2 * beta + 2 * gamma) *
      E ^ (2 * alpha + 2 * beta + 4 * delta) *
      H ^ (2 * gamma)
  let blockObj : TensorObj K 3 :=
    cyclicSymmetrization
      (TensorObj.kronFin 8 (fun r ↦
        (componentObj K 6 r).kronPow
          (profileMultiplicity alpha beta gamma delta r)))
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨N, alpha, beta, gamma, delta, hN, hsum, kept,
    (fun _ ↦ blockObj), B, hmode, ?_, hB.le, ?_, ?_⟩
  · simpa only [blockObj] using
      (mme_stothers_phi134_induced_exact_profile_blocks_restrict
        (K := K) kept hdiag)
  · intro e W hW hWB
    dsimp only [blockObj]
    exact mme_stothers_phi134_exact_profile_product_cyclic_value_below
      tau htauLower alpha beta gamma delta W hW (by
        simpa only [B, L, E, H] using hWB)
  · simpa only [B] using hweighted
