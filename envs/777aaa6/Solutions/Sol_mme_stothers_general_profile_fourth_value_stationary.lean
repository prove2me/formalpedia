-- Prove2me | solution 1 for mme_stothers_general_profile_fourth_value_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:48:31.324431+00:00
-- url     : https://prove2.me/submissions/f09efecb-f638-4c00-a743-31c35f005aa8

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_mme_stothers_general_profile_fourth_value_of_capacity_and_blocks
import Theorems.Thm_mme_stothers_general_exact_address_block_value_of_class_cyclic_values
import Theorems.Thm_mme_stothers_general_profile_outer_capacity_stationary
import Theorems.Thm_mme_stothers_general_star_degree_ratio_entropy_lower
import Theorems.Thm_mme_stothers_general_exact_target_count_factorization

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.StothersFourth.GenFinal

/-- A polynomial in the address length is eventually dominated by any strictly
geometric decay. -/
theorem poly_absorb (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (6 * ((n + 1 : ℕ) : ℝ)) ^ k * q ^ n ≤ 1 := by
  have htend : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ k * q ^ n)) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one k hq0 hq1
  have h12 : (0 : ℝ) < 1 / (12 : ℝ) ^ k := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k * q ^ n < 1 / (12 : ℝ) ^ k :=
    htend.eventually (gt_mem_nhds h12)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hbase : (6 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ 12 * (n : ℝ) := by
    push_cast
    linarith
  have hpow : ((6 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ k ≤ (12 * (n : ℝ)) ^ k := by
    have hnn : (0 : ℝ) ≤ (6 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact pow_le_pow_left₀ hnn hbase k
  have hqn : (0 : ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have h12k : (0 : ℝ) < (12 : ℝ) ^ k := by positivity
  calc ((6 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ k * q ^ n
      ≤ (12 * (n : ℝ)) ^ k * q ^ n := mul_le_mul_of_nonneg_right hpow hqn
    _ = (12 : ℝ) ^ k * ((n : ℝ) ^ k * q ^ n) := by rw [mul_pow]; ring
    _ ≤ (12 : ℝ) ^ k * (1 / (12 : ℝ) ^ k) := by
        exact mul_le_mul_of_nonneg_left hn.le h12k.le
    _ = 1 := by field_simp

end MME.StothersFourth.GenFinal

open MME.StothersFourth.GenFinal

theorem solution
    {K : Type u} [Field K]
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar))
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) →
      HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  intro V hV hVlt
  set G0 : ℝ := MME.StothersFourth.globalRate 6 tau
    (MME.StothersFourth.genProfileB base)
    (MME.StothersFourth.genProfileB base) with hG0
  set rho : ℝ :=
    MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
      MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base) with hrho
  set G : ℝ := G0 * rho with hG
  have hGpos : 0 < G := lt_of_le_of_lt hV hVlt
  set Gp : ℝ := (V + G) / 2 with hGp
  have hVGp : V < Gp := by rw [hGp]; linarith
  have hGpG : Gp < G := by rw [hGp]; linarith
  have hGp0 : 0 ≤ Gp := le_trans hV hVGp.le
  have hqlt : Gp / G < 1 := (div_lt_one hGpos).2 hGpG
  have hq0 : 0 ≤ Gp / G := div_nonneg hGp0 hGpos.le
  have hblocks :=
    mme_stothers_general_exact_address_block_value_of_class_cyclic_values
      (K := K) base tau hclass
  obtain ⟨C0, hC0, hcap0⟩ :=
    mme_stothers_general_profile_outer_capacity_stationary base bstar tau
      hbase hbstar hsame hInN
  have hNle : ∀ m : ℕ, m ≤ MME.StothersFourth.genOuterLength base m := by
    intro m
    have hs : 1 ≤ MME.StothersFourth.genProfileScale base := by
      have hb := hbase 0
      have hc : MME.StothersFourth.classMultiplicity 0 = 1 := by decide
      have : 0 < MME.StothersFourth.genProfileScale base :=
        Finset.sum_pos' (fun r _ => Nat.zero_le _)
          ⟨0, Finset.mem_univ 0, by rw [hc]; omega⟩
      omega
    simp only [MME.StothersFourth.genOuterLength]
    nlinarith
  have hNtend : Tendsto (fun m : ℕ ↦ MME.StothersFourth.genOuterLength base m)
      atTop atTop := tendsto_atTop_mono hNle tendsto_id
  have habsM := hNtend.eventually (poly_absorb (Gp / G) hq0 hqlt 145)
  have hcap : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
          MME.StothersFourth.GenInducedModeDisjoint F ∧
          Gp ^ (MME.StothersFourth.genOuterLength base m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.genProfileCount base m r)) := by
    classical
    refine ⟨C0, hC0, ?_⟩
    filter_upwards [hcap0, habsM, eventually_ge_atTop 1] with m hm habs hm1
    obtain ⟨F, hF, hcount⟩ := hm
    refine ⟨F, hF, ?_⟩
    have hratioLem := mme_stothers_general_star_degree_ratio_entropy_lower
      base bstar m hm1 hbase hbstar hsame
    set N : ℕ := MME.StothersFourth.genOuterLength base m with hN
    set P : ℝ := 6 * ((N + 1 : ℕ) : ℝ) with hP
    have hPpos : 0 < P := by
      have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos N
      rw [hP]; linarith
    have hDsPos : 0 < (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) := by
      have h1 : 1 ≤ MME.StothersFourth.genHashTargetStarDegree bstar m :=
        (mme_stothers_general_exact_target_count_factorization bstar m).2
      have : (1 : ℝ) ≤ (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) := by
        exact_mod_cast h1
      linarith
    have hDbNonneg : (0 : ℝ) ≤
        (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) := Nat.cast_nonneg _
    have hcast : (((6 * (N + 1)) ^ 100 *
        MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ) =
        P ^ 100 * (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) := by
      rw [hP]; push_cast; ring
    have hrhoPos : 0 < rho := by
      rw [hrho]
      have hEa : 0 < MME.StothersFourth.entropyProduct
          (MME.StothersFourth.genProfileB base) := by
        rw [MME.StothersFourth.entropyProduct]
        refine Finset.prod_pos fun r _ => Real.rpow_pos_of_pos ?_ _
        have hs : 0 < MME.StothersFourth.genProfileScale base := by
          have hc : MME.StothersFourth.classMultiplicity 0 = 1 := by decide
          exact Finset.sum_pos' (fun r _ => Nat.zero_le _)
            ⟨0, Finset.mem_univ 0, by rw [hc]; have := hbase 0; omega⟩
        have hD : (0 : ℝ) < (MME.StothersFourth.genProfileScale base : ℝ) := by
          exact_mod_cast hs
        have hbr : (0 : ℝ) < (base r : ℝ) := by exact_mod_cast hbase r
        simpa only [MME.StothersFourth.genProfileB] using div_pos hbr hD
      have hEb : 0 < MME.StothersFourth.entropyProduct
          (MME.StothersFourth.genProfileB bstar) := by
        rw [MME.StothersFourth.entropyProduct]
        refine Finset.prod_pos fun r _ => Real.rpow_pos_of_pos ?_ _
        have hs : 0 < MME.StothersFourth.genProfileScale bstar := by
          have hc : MME.StothersFourth.classMultiplicity 0 = 1 := by decide
          exact Finset.sum_pos' (fun r _ => Nat.zero_le _)
            ⟨0, Finset.mem_univ 0, by rw [hc]; have := hbstar 0; omega⟩
        have hD : (0 : ℝ) < (MME.StothersFourth.genProfileScale bstar : ℝ) := by
          exact_mod_cast hs
        have hbr : (0 : ℝ) < (bstar r : ℝ) := by exact_mod_cast hbstar r
        simpa only [MME.StothersFourth.genProfileB] using div_pos hbr hD
      exact div_pos hEb hEa
    have hG0pos : 0 < G0 := by
      by_contra hcon
      push_neg at hcon
      have : G0 * rho ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hrhoPos.le
      rw [← hG] at this
      linarith
    -- the retained fraction dominates rho^N / P^145
    have hRlow : rho ^ N / P ^ 145 ≤
        (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
          (((6 * (N + 1)) ^ 100 *
            MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ) := by
      rw [hcast]
      have h145 : P ^ 145 = P ^ 45 * P ^ 100 := by
        rw [← pow_add]
      have hstep : rho ^ N / (P ^ 45 * P ^ 100) ≤
          (P ^ 45 * ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
            (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ))) /
              (P ^ 45 * P ^ 100) := by
        apply div_le_div_of_nonneg_right hratioLem
        positivity
      rw [h145]
      refine hstep.trans (le_of_eq ?_)
      field_simp
    -- absorb the polynomial
    have hP145 : (0 : ℝ) < P ^ 145 := pow_pos hPpos 145
    have hGN : (0 : ℝ) < G ^ N := pow_pos hGpos N
    have hGeq : G ^ N = G0 ^ N * rho ^ N := by rw [hG, mul_pow]
    have hGpow : Gp ^ N * P ^ 145 ≤ G0 ^ N * rho ^ N := by
      have h := habs
      rw [div_pow] at h
      calc Gp ^ N * P ^ 145 = (P ^ 145 * (Gp ^ N / G ^ N)) * G ^ N := by
            field_simp
        _ ≤ 1 * G ^ N := mul_le_mul_of_nonneg_right h hGN.le
        _ = G ^ N := one_mul _
        _ = G0 ^ N * rho ^ N := hGeq
    have hG0N : (0 : ℝ) ≤ G0 ^ N := pow_nonneg hG0pos.le N
    have hmid : Gp ^ N ≤ G0 ^ N * (rho ^ N / P ^ 145) := by
      have hcalc : (G0 ^ N * (rho ^ N / P ^ 145)) * P ^ 145 = G0 ^ N * rho ^ N := by
        field_simp
      have h1 : Gp ^ N * P ^ 145 ≤ (G0 ^ N * (rho ^ N / P ^ 145)) * P ^ 145 := by
        rw [hcalc]; exact hGpow
      exact le_of_mul_le_mul_right h1 hP145
    have hkey : Gp ^ N ≤ G0 ^ N *
        ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
          (((6 * (N + 1)) ^ 100 *
            MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) :=
      hmid.trans (mul_le_mul_of_nonneg_left hRlow hG0N)
    have hexpPos : (0 : ℝ) < Real.exp
        (-C0 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := Real.exp_pos _
    calc Gp ^ N * Real.exp (-C0 * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        ≤ (G0 ^ N *
            ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
              (((6 * (N + 1)) ^ 100 *
                MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ))) *
            Real.exp (-C0 * Real.sqrt (((N + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hkey hexpPos.le
      _ ≤ (F.card : ℝ) *
            (∏ r : Fin 10,
              (MME.StothersFourth.classValue 6 tau r) ^
                (MME.StothersFourth.classMultiplicity r *
                  MME.StothersFourth.genProfileCount base m r)) := hcount
  exact mme_stothers_general_profile_fourth_value_of_capacity_and_blocks
    base hbase tau Gp hblockSupport hcap hblocks V hV hVGp
