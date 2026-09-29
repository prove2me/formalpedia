-- Prove2me | solution 1 for mme_dwz_table2_step1_interior_z_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:53:40.772753+00:00
-- url     : https://prove2.me/submissions/30c1868d-ca05-4ce2-b652-3c8ca93a312d

import Theorems.Thm_mme_dwz_table2_total_z_split_balance

open BigOperators
open MME MME.DWZStep1Histogram

set_option autoImplicit false
set_option warningAsError true

private def totalZFiberEquiv
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (k : Fin 5) (a : Fin 3) :
    TotalZFiber outer zLeft k a ≃
      (Σ s : BoundaryComponentAt k, ComponentZFiber outer zLeft s.1 a) ⊕
        InteriorZFiber outer zLeft k a where
  toFun t := by
    by_cases hb : MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0
    · exact Sum.inl
        ⟨⟨outer t.1, hb, t.2.1⟩, ⟨t.1, rfl, t.2.2⟩⟩
    · push_neg at hb
      exact Sum.inr ⟨t.1, t.2.1, hb.1, hb.2, t.2.2⟩
  invFun t := match t with
    | Sum.inl s => ⟨s.2.1, by rw [s.2.2.1]; exact ⟨s.1.2.2, s.2.2.2⟩⟩
    | Sum.inr t => ⟨t.1, t.2.1, t.2.2.2.2⟩
  left_inv t := by
    by_cases hb : MME.DWZSquare.shapeX (outer t.1) = 0 ∨
        MME.DWZSquare.shapeY (outer t.1) = 0
    · simp [hb]
    · simp [hb]
  right_inv t := by
    rcases t with s | t
    · rcases s with ⟨⟨s, hb, hz⟩, ⟨t, ht, ha⟩⟩
      cases ht
      dsimp only
      simp only [dif_pos hb]
    · rcases t with ⟨t, hz, hx, hy, ha⟩
      dsimp only
      simp [hx, hy]

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (hTotal : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber outer zLeft k a) =
        table2TotalZSplit k a * m)
    (hBoundary : ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (ComponentZFiber outer zLeft s a) =
          MME.DWZTable2Counts.split s a * m) :
    ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (InteriorZFiber outer zLeft k a) =
        MME.DWZTable2Counts.plusSplit k a * m := by
  intro k a
  have hPartition :
      Fintype.card (TotalZFiber outer zLeft k a) =
        (∑ s : BoundaryComponentAt k,
          Fintype.card (ComponentZFiber outer zLeft s.1 a)) +
        Fintype.card (InteriorZFiber outer zLeft k a) := by
    rw [Fintype.card_congr (totalZFiberEquiv outer zLeft k a),
      Fintype.card_sum, Fintype.card_sigma]
  have hBoundarySum :
      (∑ s : BoundaryComponentAt k,
        Fintype.card (ComponentZFiber outer zLeft s.1 a)) =
      (∑ s : BoundaryComponentAt k,
        MME.DWZTable2Counts.split s.1 a) * m := by
    calc
      _ = ∑ s : BoundaryComponentAt k,
          MME.DWZTable2Counts.split s.1 a * m := by
        apply Finset.sum_congr rfl
        intro s _
        exact hBoundary s.1 s.2.1 a
      _ = _ := by rw [Finset.sum_mul]
  have hBalance := congrArg (fun n : ℕ => n * m)
    (mme_dwz_table2_total_z_split_balance k a)
  change
    ((∑ s : BoundaryComponentAt k,
        MME.DWZTable2Counts.split s.1 a) +
      MME.DWZTable2Counts.plusSplit k a) * m =
      table2TotalZSplit k a * m at hBalance
  rw [Nat.add_mul] at hBalance
  rw [hTotal k a, hBoundarySum] at hPartition
  omega
