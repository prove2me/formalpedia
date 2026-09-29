-- Prove2me | Theorems.Thm_mme_dwz_table2_retained_family_rate_of_common_prime
-- name    : mme_dwz_table2_retained_family_rate_of_common_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:12:47.88351+00:00
-- url     : https://prove2.me/theorems/0512b1ec-dc33-4040-8f76-e851c59065c0
-- title:
--   Exact Table-2 retained-rate lower bound with all finite losses
-- statement:
--   At every positive integral Table-2 scale, assume the exact fixed-coarse-Z target factorization, the explicit first-hash degree and compatibility estimates, the common-prime bound, and the finite Behrend retention inequality for I surviving objects. Then 2^(retainedLogRate·L), multiplied by the fully displayed prime-floor, Behrend, and polynomial loss, is at most N_BZ·I. The right side deliberately retains the coarse-Z multinomial multiplicity N_BZ: this is the finite scalar normalization needed before a separate all-coarse-Z tensor transport realizes those copies.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equations (21) and (25), Section 6.2, printed pp. 53-59; the explicit lower-half Behrend loss is from Section 3.10; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_table2_component_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_z_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_two_branch_behrend_retained_family_lower

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_retained_family_rate_of_common_prime
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
  sorry
