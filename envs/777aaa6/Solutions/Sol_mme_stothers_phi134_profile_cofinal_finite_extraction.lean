-- Prove2me | solution 1 for mme_stothers_phi134_profile_cofinal_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:52:47.326905+00:00
-- url     : https://prove2.me/submissions/05cec464-b27f-452f-a054-05276d4469c8

import Theorems.Thm_mme_stothers_phi134_finite_power_block_certificate
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

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
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum,
      kept, block, B, _hmode, hrestrict, hB, hblock, hrate⟩ :=
    mme_stothers_phi134_finite_power_block_certificate
      (K := K) tau sigma a c htauLower htauUpper
        ha hc hcs hsa V hV hVlt
  let F : Fin kept.card → TensorObj K 3 :=
    fun j ↦ block (kept.equivFin.symm j)
  have hsumValue :
      HasTauValueAtLeast (TensorObj.bigAdd F) tau (V ^ (2 * N)) := by
    apply mme_HasTauValueAtLeast_bigAdd_uniform_strict
      F tau B hB
    · intro j W hW hWB
      exact hblock (kept.equivFin.symm j) W hW hWB
    · exact pow_nonneg hV _
    · simpa only [F] using hrate
  have hpower :
      HasTauValueAtLeast
        ((cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
            (2 * N)) tau (V ^ (2 * N)) :=
    mme_HasTauValueAtLeast_mono_restrict
      (by simpa only [F] using hrestrict) hsumValue
  have htwoN : 0 < 2 * N := Nat.mul_pos (by norm_num) hN
  have hsource :
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V :=
    mme_HasTauValueAtLeast_kronPow_root
      (cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 3 4))
      tau V (2 * N) htwoN hV hpower
  obtain ⟨s, loss, hs, hloss, _hlossPos, hextract⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 3 4))
      tau V hsource
  exact ⟨s, loss, hs, hloss, Filter.Eventually.of_forall hextract⟩
