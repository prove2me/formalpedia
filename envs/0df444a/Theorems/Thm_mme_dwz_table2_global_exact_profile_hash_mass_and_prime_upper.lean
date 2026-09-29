-- Prove2me | Theorems.Thm_mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper
-- name    : mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:53:44.682094+00:00
-- url     : https://prove2.me/theorems/cc084117-df42-44dc-9985-de9b2d961211
-- title:
--   Exact-profile Table-2 normalization for aggregate hash mass
-- statement:
--   For the DWZ Table-2 parameters at scale $L$, suppose a common prime $p$, a Behrend set $S$, the exact joint-profile multinomial, and the two entropy-controlled hash degrees satisfy the standard common-prime estimates. If the real aggregate retained mass is at least $|T||S|/(2p^2)$, then $p\leq e^{16(L+1)}$ and the retained-rate expression with the usual two-branch denominator $D_{\rm hash}$ is at most that aggregate mass. This is the quantitative normalization needed when Claim 6.8 is used in aggregate rather than pointwise form.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6 and Claim 6.8; aggregate-mass analogue of the accepted exact-profile retained-count normalization.

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper
    (m : ℕ) (hm : 0 < m)
    (profileCard fixedTargetCard d Q p : ℕ) (R mass : ℝ)
    (S : Finset ℕ)
    (hprofileCard : profileCard =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m))
    (hfactor :
      Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
        Nat.multinomial Finset.univ
            (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
          fixedTargetCard)
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
        (fixedTargetCard : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP))
    (hp : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R))
    (hdPow : d ≤ 15 ^ (MME.DWZTable2Counts.scale * m))
    (hQPow : Q ≤ 15 ^ (MME.DWZTable2Counts.scale * m))
    (hpNat : p ≤ 2 * max 4 (8 * max d Q))
    (hbehrend :
      ((p / 2 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
        (S.card : ℝ))
    (hretained :
      ((profileCard : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ mass) :
    let L := MME.DWZTable2Counts.scale * m
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let Dhash : ℝ :=
      32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
    (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
      Real.rpow 2
            (MME.DWZSquare.retainedLogRate * ((L : ℕ) : ℝ)) *
          (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
            Dhash ≤ mass := by
  sorry
