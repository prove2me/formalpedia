-- Prove2me | solution 1 for mme_dwz_table2_z_multinomial_entropy_polynomial_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:49:25.212814+00:00
-- url     : https://prove2.me/submissions/682c28a3-ad88-4971-9c5c-9426a6d724ee

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true

private theorem z_normalized :
    (fun k : Fin 5 =>
      (MME.DWZTable2Counts.alphaZ k : ℝ) /
        (MME.DWZTable2Counts.scale : ℝ)) =
      mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha := by
  funext k
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨_, _, _, _, _, _, _, _, hAlphaZ, _⟩
  apply (div_eq_iff (by
    norm_num [MME.DWZTable2Counts.scale] :
      (MME.DWZTable2Counts.scale : ℝ) ≠ 0)).2
  simpa only [mul_comm] using (hAlphaZ k).symm

theorem solution (m : ℕ) (hm : 0 < m) :
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeZ
              MME.DWZSquare.alpha)) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 5 *
        (Nat.multinomial Finset.univ
          (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) : ℝ) := by
  have hsum :
      ∑ k : Fin 5, MME.DWZTable2Counts.alphaZ k =
        MME.DWZTable2Counts.scale :=
    mme_dwz_table2_integer_counts_exact.2.2.2.2.2.1
  have hsumPos :
      0 < ∑ k : Fin 5, MME.DWZTable2Counts.alphaZ k := by
    rw [hsum]
    norm_num [MME.DWZTable2Counts.scale]
  have h := mme_dwz_multinomial_entropy_polynomial_lower
    MME.DWZTable2Counts.alphaZ m hm hsumPos
  rw [hsum, z_normalized] at h
  simpa only [Fintype.card_fin, mul_assoc] using h
