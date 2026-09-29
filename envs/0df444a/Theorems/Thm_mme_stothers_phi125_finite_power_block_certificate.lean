-- Prove2me | Theorems.Thm_mme_stothers_phi125_finite_power_block_certificate
-- name    : mme_stothers_phi125_finite_power_block_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:10:44.407319+00:00
-- url     : https://prove2.me/theorems/8dea170c-7a4d-4bdb-b11d-4011e50217d0
-- title:
--   Finite retained-block certificate for a feasible phi_125 profile
-- statement:
--   Fix a feasible positive Davie–Stothers φ₁₂₅ profile with normalized parameters a,b and γ-frequency 1−a−b. For every nonnegative V strictly below the corresponding unoptimized profile rate, there is a positive integral scale N, integers α+β+γ=N, and a retained cyclic exact-profile family F whose three mode projections are injective. Its surviving tensor blocks form a direct-sum restriction into the 2N-th power of the cyclic φ₁₂₅ constituent. For some common nonnegative block base B, each block attains every strict lower tau-value and $$V^{2N}<|F|B.$$ This is the finite certificate produced by integral rounding, type-2 Salem–Spencer hashing, induced block zeroing, and the six fine-component estimates in Davie–Stothers Lemma 5.1(ii).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Lemma 5.1(ii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_finite_power_block_certificate
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
    ∃ (N alpha beta gamma : ℕ),
      0 < N ∧ alpha + beta + gamma = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  sorry
