-- Prove2me | solution 1 for mme_stothers_phi233_rounded_tail_completion_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:04:51.118313+00:00
-- url     : https://prove2.me/submissions/435dcf6e-cde6-4e01-a620-2b1f17bcdcde

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_rounded_completion_ratio_subexponential
import Theorems.Thm_mme_stothers_phi233_stationary_profile_sequence_exists

open MME Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option warningAsError true

/-- The stationary completion profiles needed in the asymptotic count can
be selected automatically after discarding a finite prefix of any rounded
positive stationary target sequence. -/
theorem solution
    (A B C D : ℕ → ℕ) (a b c d : ℝ)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hsigmaUpper : 2 * a + b < 2 / 3)
    (hmuUpper : a + c < 1 / 2)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    ∃ k : ℕ, 0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (Nat.card
              (MME.StothersFourth.Phi233.MarginalAddress
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))) : ℝ) ≤
            (((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
              Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
              (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10 *
              (Nat.card
                (MME.StothersFourth.Phi233.ExactProfileAddress
                  (n + k) (A (n + k)) (B (n + k))
                  (C (n + k)) (D (n + k))) : ℝ) := by
  let Ar : ℕ → ℝ := fun n ↦ (A n : ℝ) / (n : ℝ)
  let Br : ℕ → ℝ := fun n ↦ (B n : ℝ) / (n : ℝ)
  let Cr : ℕ → ℝ := fun n ↦ (C n : ℝ) / (n : ℝ)
  let Dr : ℕ → ℝ := fun n ↦ (D n : ℝ) / (n : ℝ)
  let sigma : ℕ → ℝ := fun n ↦ 2 * Ar n + Br n
  let mu : ℕ → ℝ := fun n ↦ Ar n + Cr n
  have hAr : Tendsto Ar atTop (nhds a) := by simpa only [Ar] using hA
  have hBr : Tendsto Br atTop (nhds b) := by simpa only [Br] using hB
  have hCr : Tendsto Cr atTop (nhds c) := by simpa only [Cr] using hC
  have hDr : Tendsto Dr atTop (nhds d) := by simpa only [Dr] using hD
  have hSigma : Tendsto sigma atTop (nhds (2 * a + b)) := by
    simpa only [sigma] using (hAr.const_mul 2).add hBr
  have hMu : Tendsto mu atTop (nhds (a + c)) := by
    simpa only [mu] using hAr.add hCr
  have hCompat : Tendsto (fun n ↦ sigma n / 2 + mu n) atTop
      (nhds ((2 * a + b) / 2 + (a + c))) :=
    (hSigma.div_const 2).add hMu
  have hsigma0 : 0 < 2 * a + b := by linarith
  have hmu0 : 0 < a + c := by linarith
  have hcompatLimit : (2 * a + b) / 2 + (a + c) < 1 := by
    nlinarith
  have hgood : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < sigma n ∧ sigma n < 2 / 3 ∧
        0 < mu n ∧ mu n < 1 / 2 ∧ sigma n / 2 + mu n < 1 := by
    filter_upwards [eventually_gt_atTop 0,
      hSigma.eventually_const_lt hsigma0,
      hSigma.eventually_lt_const hsigmaUpper,
      hMu.eventually_const_lt hmu0,
      hMu.eventually_lt_const hmuUpper,
      hCompat.eventually_lt_const hcompatLimit] with n hn hs0 hsU hm0 hmU hcomp
    exact ⟨hn, hs0, hsU, hm0, hmU, hcomp⟩
  obtain ⟨k, hk⟩ := (eventually_atTop.1 hgood)
  have hshift (n : ℕ) :
      0 < n + k ∧ 0 < sigma (n + k) ∧ sigma (n + k) < 2 / 3 ∧
        0 < mu (n + k) ∧ mu (n + k) < 1 / 2 ∧
          sigma (n + k) / 2 + mu (n + k) < 1 := by
    exact hk (n + k) (by omega)
  let sigmaShift : ℕ → ℝ := fun n ↦ sigma (n + k)
  let muShift : ℕ → ℝ := fun n ↦ mu (n + k)
  obtain ⟨X, Y, Z, W, hX, hY, hZ, hW, htotalX, hsigmaX, hmuX,
      hcritical⟩ :=
    mme_stothers_phi233_stationary_profile_sequence_exists
      sigmaShift muShift
      (fun n ↦ by simpa only [sigmaShift] using (hshift n).2.1)
      (fun n ↦ by simpa only [muShift] using (hshift n).2.2.2.1)
      (fun n ↦ by
        have h := (hshift n).2.2.1
        dsimp only [sigmaShift]
        linarith)
      (fun n ↦ by
        simpa only [sigmaShift, muShift] using (hshift n).2.2.2.2.2)
  have hRatio :=
    mme_stothers_phi233_rounded_completion_ratio_subexponential
      (fun n ↦ n + k) (fun n ↦ A (n + k)) (fun n ↦ B (n + k))
      (fun n ↦ C (n + k)) (fun n ↦ D (n + k)) X Y Z W a b c d
      (fun n ↦ (hshift n).1)
      (fun n ↦ hsum (n + k)) ha hb hc hd htotal hstation
      (by simpa only [Ar] using hAr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Br] using hBr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Cr] using hCr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Dr] using hDr.comp (tendsto_add_atTop_nat k))
      hX hY hZ hW htotalX
      (by simpa only [sigmaShift, sigma, Ar, Br] using hsigmaX)
      (by simpa only [muShift, mu, Ar, Cr] using hmuX)
      (fun n ↦ by
        simpa only [sigma, Ar, Br] using (hshift n).2.2.1)
      (fun n ↦ by
        simpa only [mu, Ar, Cr] using (hshift n).2.2.2.2.1)
      hcritical
  exact ⟨k, (hk k (by omega)).1, hRatio⟩
