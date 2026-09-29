-- Prove2me | solution 1 for mme_dwz_table2_component_multinomial_entropy_polynomial_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:48:35.634754+00:00
-- url     : https://prove2.me/submissions/8cb63118-a83a-4cb0-9c67-1d28be9f9b69

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true

private theorem component_normalized :
    (fun s : Fin 15 =>
      (MME.DWZTable2Counts.component s : ℝ) /
        (MME.DWZTable2Counts.scale : ℝ)) = MME.DWZSquare.alpha := by
  funext s
  rcases mme_dwz_table2_integer_counts_exact with ⟨hcomponent, _⟩
  apply (div_eq_iff (by
    norm_num [MME.DWZTable2Counts.scale] :
      (MME.DWZTable2Counts.scale : ℝ) ≠ 0)).2
  simpa only [mul_comm] using (hcomponent s).symm

theorem solution (m : ℕ) (hm : 0 < m) :
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits MME.DWZSquare.alpha) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 15 *
        (Nat.multinomial Finset.univ
          (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) : ℝ) := by
  have hsum :
      ∑ s : Fin 15, MME.DWZTable2Counts.component s =
        MME.DWZTable2Counts.scale :=
    mme_dwz_table2_integer_counts_exact.2.2.2.1
  have hsumPos :
      0 < ∑ s : Fin 15, MME.DWZTable2Counts.component s := by
    rw [hsum]
    norm_num [MME.DWZTable2Counts.scale]
  have h := mme_dwz_multinomial_entropy_polynomial_lower
    MME.DWZTable2Counts.component m hm hsumPos
  rw [hsum, component_normalized] at h
  simpa only [Fintype.card_fin, mul_assoc] using h
