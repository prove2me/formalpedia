-- Prove2me | solution 1 for mme_stothers_general_star_degree_ratio_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:37:44.278101+00:00
-- url     : https://prove2.me/submissions/586e6ca5-c3e4-4459-9e04-74ac35f70bb9

import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_stothers_general_support_entropy_eq_entropyProduct

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace MME.StothersFourth.GenRatio

private theorem orbit_unique (sigma : GenHashSupportTriple) :
    (Finset.univ.filter
      (fun r : Fin 10 ↦ genSameOrbitExplicit sigma.1 (classRep r))).card = 1 := by
  revert sigma
  decide

private theorem joint_pos (b : Fin 10 → ℕ) (hb : ∀ r, 0 < b r)
    (sigma : GenHashSupportTriple) : 0 < genJointMultiplicity b 1 sigma.1 := by
  classical
  obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp (orbit_unique sigma)
  have hJ : genJointMultiplicity b 1 sigma.1 = b r0 := by
    simp only [genJointMultiplicity, ← Finset.sum_filter]
    rw [hr0, Finset.sum_singleton, genProfileCount, mul_one]
  rw [hJ]
  exact hb r0

private theorem joint_scale (b : Fin 10 → ℕ) (m : ℕ) (sigma : Fin 3 → Fin 9) :
    genJointMultiplicity b m sigma = genJointMultiplicity b 1 sigma * m := by
  simp only [genJointMultiplicity, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases h : genSameOrbitExplicit sigma (classRep r)
  · simp [h, genProfileCount]
  · simp [h]

/-- The forty-five joint multiplicities sum to the address length. -/
private theorem support_sum (b : Fin 10 → ℕ) (m : ℕ) :
    (∑ sigma : GenHashSupportTriple, genHashTargetJointTable b m sigma) =
      genOuterLength b m := by
  classical
  have hfiber :
      (∑ sigma : GenHashSupportTriple, genHashTargetJointTable b m sigma) =
        ∑ j : Fin 9,
          ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
            genHashTargetJointTable b m sigma.1 := by
    calc
      (∑ sigma : GenHashSupportTriple, genHashTargetJointTable b m sigma) =
          ∑ x : Sigma fun j : Fin 9 ↦
            {sigma : GenHashSupportTriple // sigma.1 0 = j},
            genHashTargetJointTable b m x.2.1 := by
        exact (Equiv.sum_comp
          (Equiv.sigmaFiberEquiv (fun sigma : GenHashSupportTriple ↦ sigma.1 0))
          (fun sigma : GenHashSupportTriple ↦
            genHashTargetJointTable b m sigma)).symm
      _ = ∑ j : Fin 9,
            ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
              genHashTargetJointTable b m sigma.1 :=
        Fintype.sum_sigma _
  rw [hfiber]
  have hrow : ∀ j : Fin 9,
      (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
        genHashTargetJointTable b m sigma.1) = genMarginalCount b m j :=
    fun j => mme_stothers_general_outer_profile_arithmetic.2.2.2 b m 0 j
  rw [Finset.sum_congr rfl (fun j _ => hrow j)]
  simp only [genMarginalCount]
  rw [← Finset.sum_mul, mme_stothers_general_outer_profile_arithmetic.2.1 b]
  simp only [genOuterLength]
  ac_rfl

private theorem row_div (b : Fin 10 → ℕ) (m : ℕ) :
    (∏ sigma : GenHashSupportTriple,
        (genHashTargetJointTable b m sigma).factorial) ∣
      ∏ j : Fin 9, (genMarginalCount b m j).factorial := by
  classical
  have hrowDiv (j : Fin 9) :
      (∏ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
          (genHashTargetJointTable b m sigma.1).factorial) ∣
        (genMarginalCount b m j).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset {sigma : GenHashSupportTriple // sigma.1 0 = j})
      (fun sigma ↦ genHashTargetJointTable b m sigma.1)
    simpa [mme_stothers_general_outer_profile_arithmetic.2.2.2 b m 0 j] using h
  have hpart :
      (∏ j : Fin 9,
        ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
          (genHashTargetJointTable b m sigma.1).factorial) =
        ∏ sigma : GenHashSupportTriple,
          (genHashTargetJointTable b m sigma).factorial := by
    calc
      (∏ j : Fin 9,
          ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 0 = j},
            (genHashTargetJointTable b m sigma.1).factorial) =
          ∏ x : Sigma fun j : Fin 9 ↦
            {sigma : GenHashSupportTriple // sigma.1 0 = j},
            (genHashTargetJointTable b m x.2.1).factorial := by
        exact (Fintype.prod_sigma
          (fun x : Sigma fun j : Fin 9 ↦
            {sigma : GenHashSupportTriple // sigma.1 0 = j} ↦
            (genHashTargetJointTable b m x.2.1).factorial)).symm
      _ = ∏ sigma : GenHashSupportTriple,
            (genHashTargetJointTable b m sigma).factorial := by
        simpa only using
          (Equiv.prod_comp
            (Equiv.sigmaFiberEquiv
              (fun sigma : GenHashSupportTriple ↦ sigma.1 0))
            (fun sigma : GenHashSupportTriple ↦
              (genHashTargetJointTable b m sigma).factorial))
  rw [← hpart]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hrowDiv j

private theorem star_cast (b : Fin 10 → ℕ) (m : ℕ) :
    (genHashTargetStarDegree b m : ℝ) =
      ((∏ j : Fin 9, (genMarginalCount b m j).factorial : ℕ) : ℝ) /
        ((∏ sigma : GenHashSupportTriple,
          (genHashTargetJointTable b m sigma).factorial : ℕ) : ℝ) := by
  have hBpos : (0 : ℕ) < ∏ sigma : GenHashSupportTriple,
      (genHashTargetJointTable b m sigma).factorial :=
    Finset.prod_pos fun _ _ => Nat.factorial_pos _
  have hne : ((∏ sigma : GenHashSupportTriple,
      (genHashTargetJointTable b m sigma).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hBpos.ne'
  simpa only [genHashTargetStarDegree] using Nat.cast_div (row_div b m) hne

private theorem factorial_prod_mult (b : Fin 10 → ℕ) (m : ℕ) :
    (∏ sigma : GenHashSupportTriple,
        (genHashTargetJointTable b m sigma).factorial) *
      Nat.multinomial Finset.univ
        (fun sigma : GenHashSupportTriple ↦ genHashTargetJointTable b m sigma) =
      (genOuterLength b m).factorial := by
  have h := Nat.multinomial_spec (Finset.univ : Finset GenHashSupportTriple)
    (fun sigma ↦ genHashTargetJointTable b m sigma)
  rw [support_sum b m] at h
  exact h

end MME.StothersFourth.GenRatio

open MME.StothersFourth.GenRatio

theorem solution
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j) :
    (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
        MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) ^
        (MME.StothersFourth.genOuterLength base m) ≤
      (6 * ((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ)) ^ 45 *
        ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
          (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ)) := by
  classical
  have hscale : MME.StothersFourth.genProfileScale bstar =
      MME.StothersFourth.genProfileScale base := by
    have h : (∑ j : Fin 9, MME.StothersFourth.genMarginalBaseCount bstar j) =
        ∑ j : Fin 9, MME.StothersFourth.genMarginalBaseCount base j :=
      Finset.sum_congr rfl (fun j _ => hsame j)
    rw [mme_stothers_general_outer_profile_arithmetic.2.1 bstar,
      mme_stothers_general_outer_profile_arithmetic.2.1 base] at h
    omega
  have hmarg : ∀ (k : ℕ) (j : Fin 9),
      MME.StothersFourth.genMarginalCount bstar k j =
        MME.StothersFourth.genMarginalCount base k j := by
    intro k j
    simp only [MME.StothersFourth.genMarginalCount, hsame j]
  have hlen : ∀ k : ℕ, MME.StothersFourth.genOuterLength bstar k =
      MME.StothersFourth.genOuterLength base k := by
    intro k
    simp only [MME.StothersFourth.genOuterLength, hscale]
  have hscalePos : 0 < MME.StothersFourth.genProfileScale base := by
    have hb := hbase 0
    have hc : MME.StothersFourth.classMultiplicity 0 = 1 := by decide
    exact Finset.sum_pos' (fun r _ => Nat.zero_le _)
      ⟨0, Finset.mem_univ 0, by rw [hc]; omega⟩
  have hcard : Fintype.card MME.StothersFourth.GenHashSupportTriple = 45 := by decide
  set N : ℕ := MME.StothersFourth.genOuterLength base m with hN
  set W : ℕ := MME.StothersFourth.genOuterLength base 1 with hWdef
  have hNW : N = W * m := by
    simp only [hN, hWdef, MME.StothersFourth.genOuterLength]
    ring
  have hWpos : 0 < W := by
    simp only [hWdef, MME.StothersFourth.genOuterLength]
    omega
  set M : ℕ := ∏ j : Fin 9,
    (MME.StothersFourth.genMarginalCount base m j).factorial with hM
  set Bb : ℕ := ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
    (MME.StothersFourth.genHashTargetJointTable base m sigma).factorial with hBb
  set Bs : ℕ := ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
    (MME.StothersFourth.genHashTargetJointTable bstar m sigma).factorial with hBs
  have hMpos : 0 < M := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  have hBbpos : 0 < Bb := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  have hBspos : 0 < Bs := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  have hMs : (∏ j : Fin 9,
      (MME.StothersFourth.genMarginalCount bstar m j).factorial) = M :=
    Finset.prod_congr rfl (fun j _ => by rw [hmarg m j])
  have hstarb : (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) =
      (M : ℝ) / (Bb : ℝ) := star_cast base m
  have hstars : (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) =
      (M : ℝ) / (Bs : ℝ) := by
    rw [star_cast bstar m, hMs]
  set multb : ℕ := Nat.multinomial Finset.univ
    (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
      MME.StothersFourth.genHashTargetJointTable base m sigma) with hmultb
  set mults : ℕ := Nat.multinomial Finset.univ
    (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
      MME.StothersFourth.genHashTargetJointTable bstar m sigma) with hmults
  have hmultbpos : 0 < multb := Nat.multinomial_pos _ _
  have hmultspos : 0 < mults := Nat.multinomial_pos _ _
  have hfb : Bb * multb = N.factorial := factorial_prod_mult base m
  have hfs : Bs * mults = N.factorial := by
    have h := factorial_prod_mult bstar m
    rwa [hlen m] at h
  have hratio :
      (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
        (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) =
        (multb : ℝ) / (mults : ℝ) := by
    have hcast : (Bb : ℝ) * (multb : ℝ) = (Bs : ℝ) * (mults : ℝ) := by
      exact_mod_cast hfb.trans hfs.symm
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
    have hBbR : (Bb : ℝ) ≠ 0 := by exact_mod_cast hBbpos.ne'
    have hBsR : (Bs : ℝ) ≠ 0 := by exact_mod_cast hBspos.ne'
    have hmsR : (mults : ℝ) ≠ 0 := by exact_mod_cast hmultspos.ne'
    have h1 : (M : ℝ) / (Bb : ℝ) / ((M : ℝ) / (Bs : ℝ)) = (Bs : ℝ) / (Bb : ℝ) := by
      field_simp
    have h2 : (Bs : ℝ) / (Bb : ℝ) = (multb : ℝ) / (mults : ℝ) := by
      rw [div_eq_div_iff hBbR hmsR, ← hcast, mul_comm]
    rw [hstarb, hstars, h1, h2]
  rw [hratio]
  set Ea : ℝ := MME.StothersFourth.entropyProduct
    (MME.StothersFourth.genProfileB base) with hEa
  set Eb : ℝ := MME.StothersFourth.entropyProduct
    (MME.StothersFourth.genProfileB bstar) with hEb
  have hEapos : 0 < Ea := by
    rw [hEa, MME.StothersFourth.entropyProduct]
    refine Finset.prod_pos fun r _ => Real.rpow_pos_of_pos ?_ _
    have hD : (0 : ℝ) < (MME.StothersFourth.genProfileScale base : ℝ) := by
      exact_mod_cast hscalePos
    have hbr : (0 : ℝ) < (base r : ℝ) := by exact_mod_cast hbase r
    simpa only [MME.StothersFourth.genProfileB] using div_pos hbr hD
  have hEbpos : 0 < Eb := by
    rw [hEb, MME.StothersFourth.entropyProduct]
    refine Finset.prod_pos fun r _ => Real.rpow_pos_of_pos ?_ _
    have hD : (0 : ℝ) < (MME.StothersFourth.genProfileScale bstar : ℝ) := by
      rw [hscale]; exact_mod_cast hscalePos
    have hbr : (0 : ℝ) < (bstar r : ℝ) := by exact_mod_cast hbstar r
    simpa only [MME.StothersFourth.genProfileB] using div_pos hbr hD
  have hwsumb : (∑ sigma : MME.StothersFourth.GenHashSupportTriple,
      MME.StothersFourth.genHashTargetJointTable base 1 sigma) = W :=
    support_sum base 1
  have hwsums : (∑ sigma : MME.StothersFourth.GenHashSupportTriple,
      MME.StothersFourth.genHashTargetJointTable bstar 1 sigma) = W := by
    rw [support_sum bstar 1, hlen 1]
  have hwmb : (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
      MME.StothersFourth.genHashTargetJointTable base 1 sigma * m) =
      fun sigma ↦ MME.StothersFourth.genHashTargetJointTable base m sigma := by
    funext sigma
    exact (joint_scale base m sigma.1).symm
  have hwms : (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
      MME.StothersFourth.genHashTargetJointTable bstar 1 sigma * m) =
      fun sigma ↦ MME.StothersFourth.genHashTargetJointTable bstar m sigma := by
    funext sigma
    exact (joint_scale bstar m sigma.1).symm
  have hidb := mme_stothers_general_support_entropy_eq_entropyProduct base hbase
  have hids := mme_stothers_general_support_entropy_eq_entropyProduct bstar hbstar
  rw [← hEa, ← hWdef] at hidb
  rw [← hEb, hlen 1, ← hWdef] at hids
  have hrewb : (m : ℝ) * ((W : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
          (MME.StothersFourth.genHashTargetJointTable base 1 sigma : ℝ) /
            ((W : ℕ) : ℝ))) = (N : ℝ) * (Real.log 3 - Real.log Ea) := by
    rw [mul_assoc ((W : ℝ)) (Real.log 2), hidb, hNW]
    push_cast
    ring
  have hrews : (m : ℝ) * ((W : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
          (MME.StothersFourth.genHashTargetJointTable bstar 1 sigma : ℝ) /
            ((W : ℕ) : ℝ))) = (N : ℝ) * (Real.log 3 - Real.log Eb) := by
    rw [mul_assoc ((W : ℝ)) (Real.log 2), hids, hNW]
    push_cast
    ring
  have hlowb :
      Real.exp ((N : ℝ) * (Real.log 3 - Real.log Ea)) ≤
        (6 * ((N + 1 : ℕ) : ℝ)) ^ 45 * (multb : ℝ) := by
    have hraw := mme_dwz_multinomial_entropy_polynomial_lower
      (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
        MME.StothersFourth.genHashTargetJointTable base 1 sigma) m hm
      (by rw [hwsumb]; exact hWpos)
    rw [hwsumb, hcard, hwmb, ← hNW, hrewb] at hraw
    exact hraw
  have hupps :
      (mults : ℝ) ≤ Real.exp ((N : ℝ) * (Real.log 3 - Real.log Eb)) := by
    have hraw := mme_dwz_multinomial_entropy_upper
      (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
        MME.StothersFourth.genHashTargetJointTable bstar 1 sigma) m hm
      (by rw [hwsums]; exact hWpos)
    rw [hwsums, hwms, hrews] at hraw
    exact hraw
  have hexps : (0 : ℝ) < Real.exp ((N : ℝ) * (Real.log 3 - Real.log Eb)) :=
    Real.exp_pos _
  have hpowEq : (Eb / Ea) ^ N =
      Real.exp ((N : ℝ) * (Real.log 3 - Real.log Ea)) /
        Real.exp ((N : ℝ) * (Real.log 3 - Real.log Eb)) := by
    rw [← Real.exp_sub]
    have hsub : (N : ℝ) * (Real.log 3 - Real.log Ea) -
        (N : ℝ) * (Real.log 3 - Real.log Eb) =
        (N : ℝ) * (Real.log Eb - Real.log Ea) := by ring
    rw [hsub, Real.exp_nat_mul, ← Real.log_div hEbpos.ne' hEapos.ne',
      Real.exp_log (div_pos hEbpos hEapos)]
  rw [hpowEq, div_le_iff₀ hexps]
  set P : ℝ := (6 * ((N + 1 : ℕ) : ℝ)) ^ 45 with hP
  have hbasenn : (0 : ℝ) ≤ 6 * ((N + 1 : ℕ) : ℝ) := by
    have h6 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hPnonneg : (0 : ℝ) ≤ P := by
    rw [hP]
    exact pow_nonneg hbasenn 45
  have hq : (0 : ℝ) ≤ (multb : ℝ) / (mults : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnn : (0 : ℝ) ≤ P * ((multb : ℝ) / (mults : ℝ)) := mul_nonneg hPnonneg hq
  have hstep := mul_le_mul_of_nonneg_left hupps hnn
  have hmsR : (mults : ℝ) ≠ 0 := by exact_mod_cast hmultspos.ne'
  have hcancel : P * ((multb : ℝ) / (mults : ℝ)) * (mults : ℝ) = P * (multb : ℝ) := by
    field_simp
  linarith [hlowb, hstep, hcancel]
