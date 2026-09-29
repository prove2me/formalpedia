-- Prove2me | solution 1 for mme_dwz_table2_retained_family_rate_of_common_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:22:30.47564+00:00
-- url     : https://prove2.me/submissions/32bdf79b-ecfc-4e55-a323-dec4eb270682

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_table2_component_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_z_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_two_branch_behrend_retained_family_lower

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem common_prime_upper_of_positive_degree
    (d p : ℕ) (R : ℝ) (hd : 0 < d)
    (hp : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R)) :
    (p : ℝ) ≤ 16 * max (d : ℝ) R := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmax1 : (1 : ℝ) ≤ max (d : ℝ) R :=
    hd1.trans (le_max_left _ _)
  have h8 : (8 : ℝ) ≤ 16 * max (d : ℝ) R := by nlinarith
  simpa [max_eq_right h8] using hp

private theorem exp_two_branch_eq_retained_rpow (m : ℕ) :
    let L : ℝ := ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)
    let c : ℝ := L * Real.log 2
    Real.exp
        (min
          (c * mme_modern_entropyBits MME.DWZSquare.alpha -
            c * (MME.DWZSquare.maxSameMarginalEntropy -
              mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeX
                  MME.DWZSquare.alpha)))
          (c * mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeZ
                  MME.DWZSquare.alpha) -
            c * MME.DWZSquare.logAlphaP)) =
      Real.rpow 2 (MME.DWZSquare.retainedLogRate * L) := by
  dsimp only
  let L : ℝ := ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)
  let c : ℝ := L * Real.log 2
  let a : ℝ :=
    mme_modern_entropyBits MME.DWZSquare.alpha +
      mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha) -
      MME.DWZSquare.maxSameMarginalEntropy
  let b : ℝ :=
    mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha) -
      MME.DWZSquare.logAlphaP
  have hc : 0 ≤ c := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hleft :
      c * mme_modern_entropyBits MME.DWZSquare.alpha -
          c * (MME.DWZSquare.maxSameMarginalEntropy -
            mme_modern_entropyBits
              (mme_modern_marginal MME.DWZSquare.shapeX
                MME.DWZSquare.alpha)) = c * a := by
    dsimp only [a]
    ring
  have hright :
      c * mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeZ
              MME.DWZSquare.alpha) -
          c * MME.DWZSquare.logAlphaP = c * b := by
    dsimp only [b]
    ring
  rw [hleft, hright]
  have hmin : min (c * a) (c * b) = c * min a b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, min_eq_left (mul_le_mul_of_nonneg_left hab hc)]
    · rw [min_eq_right hba, min_eq_right (mul_le_mul_of_nonneg_left hba hc)]
  rw [hmin]
  change Real.exp (c * min a b) =
    (2 : ℝ) ^ (MME.DWZSquare.retainedLogRate * L)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold MME.DWZSquare.retainedLogRate
  change Real.exp (c * min a b) =
    Real.exp (Real.log 2 * (min a b * L))
  congr 1
  dsimp only [c]
  ring

theorem solution
    (m : ℕ) (hm : 0 < m) (T d p I : ℕ) (R : ℝ)
    (hfactor :
      Nat.multinomial Finset.univ
          (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
        Nat.multinomial Finset.univ
            (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) * T)
    (hdpos : 0 < d) (hppos : 0 < p)
    (hd : (d : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 5 *
        (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 15 *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            (MME.DWZSquare.maxSameMarginalEntropy -
              mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeX
                  MME.DWZSquare.alpha))))
    (hR : R =
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (T : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP))
    (hp : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R))
    (hretained :
      ((T : ℝ) *
          (((p / 2 : ℕ) : ℝ) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (2 * (p : ℝ) ^ 2) ≤ (I : ℝ)) :
    let L := MME.DWZTable2Counts.scale * m
    let jointPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 15
    let degreePoly : ℝ :=
      (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 * (((L + 1 : ℕ) : ℝ)) ^ 15
    let zPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 5
    let compatibilityPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 9
    Real.rpow 2
          (MME.DWZSquare.retainedLogRate * ((L : ℕ) : ℝ)) *
        (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (32 * max (jointPoly * degreePoly)
            (zPoly * compatibilityPoly)) ≤
      (Nat.multinomial Finset.univ
        (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) : ℝ) * (I : ℝ) := by
  dsimp only
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let jointPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 15
  let degreePoly : ℝ :=
    (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 * (((L + 1 : ℕ) : ℝ)) ^ 15
  let zPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 5
  let compatibilityPoly : ℝ := (6 * (((L + 1 : ℕ) : ℝ))) ^ 9
  let Nalpha : ℕ := Nat.multinomial Finset.univ
    (fun s : Fin 15 => MME.DWZTable2Counts.component s * m)
  let NBZ : ℕ := Nat.multinomial Finset.univ
    (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m)
  let c : ℝ := (L : ℝ) * Real.log 2
  have hA := mme_dwz_table2_component_multinomial_entropy_polynomial_lower m hm
  have hZ := mme_dwz_table2_z_multinomial_entropy_polynomial_lower m hm
  have hp' := common_prime_upper_of_positive_degree d p R hdpos hp
  have hbase := mme_dwz_two_branch_behrend_retained_family_lower
    Nalpha NBZ T d p I R jointPoly degreePoly zPoly compatibilityPoly
    (c * mme_modern_entropyBits MME.DWZSquare.alpha)
    (c * mme_modern_entropyBits
      (mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha))
    (c * (MME.DWZSquare.maxSameMarginalEntropy -
      mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha)))
    (c * MME.DWZSquare.logAlphaP)
    hfactor hdpos hppos
    (by dsimp only [jointPoly, L]; positivity)
    (by dsimp only [degreePoly, L]; positivity)
    (by dsimp only [zPoly, L]; positivity)
    (by dsimp only [compatibilityPoly, L]; positivity)
    (by simpa only [Nalpha, jointPoly, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hA)
    (by simpa only [NBZ, zPoly, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hZ)
    (by simpa only [degreePoly, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hd)
    (by simpa only [compatibilityPoly, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hR)
    hp' hretained
  rw [exp_two_branch_eq_retained_rpow m] at hbase
  simpa only [Nalpha, NBZ, jointPoly, degreePoly, zPoly,
    compatibilityPoly, L] using hbase
