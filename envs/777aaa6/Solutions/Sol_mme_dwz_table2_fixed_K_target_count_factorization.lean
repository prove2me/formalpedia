-- Prove2me | solution 1 for mme_dwz_table2_fixed_K_target_count_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:50:23.879092+00:00
-- url     : https://prove2.me/submissions/7adf4a8f-b245-46df-81ff-97933250434e

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    (hK : ∀ k,
      Fintype.card {t // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m) :
    let Outer :=
      {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m}
    Nat.multinomial Finset.univ
        (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
      Nat.multinomial Finset.univ
          (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) *
        Nat.card Outer := by
  classical
  dsimp only
  have hPush (k : Fin 5) :
      (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
          MME.DWZTable2Counts.component s.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    rw [← Finset.sum_mul]
    congr 1
    fin_cases k <;> decide
  exact (mme_dwz_lemma6_7_typical_denominator_count
    MME.DWZSquare.shapeZ K
    (fun s : Fin 15 => MME.DWZTable2Counts.component s * m)
    (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m)
    hK hPush).2
