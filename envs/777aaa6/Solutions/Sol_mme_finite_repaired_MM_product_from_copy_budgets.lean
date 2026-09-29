-- Prove2me | solution 1 for mme_finite_repaired_MM_product_from_copy_budgets
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T12:08:06.642557+00:00
-- url     : https://prove2.me/submissions/8f901a70-cd7b-46f6-844c-b8d9008cdfde

import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_bigAdd_prefix_restrict

open BigOperators MME MME.TensorObj
set_option autoImplicit false
universe u

private theorem product_of_sums {K : Type u} [Field K] {k : ℕ}
    (a b c copies : Fin k → ℕ) :
    Isomorphic
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (copies j) ↦ MMObj K (a j) (b j) (c j))))
      (bigAdd (fun _ : Fin (∏ j, copies j) ↦ MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j))) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_bigAdd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod]
  congr 1
  rw [← mme_toQ_kronFin]
  exact TensorQ.toQ_eq_iff.mpr (mme_kronFin_MMObj_iso k a b c)

theorem solution {K : Type u} [Field K] {k R : ℕ}
    (a b c counts repair : Fin k → ℕ)
    (hpos : ∀ j, 0 < repair j)
    (henough : ∀ j, repair j ≤ counts j)
    (hR : (∏ j, 2 * repair j) ≤ R) :
    Restrict
      (bigAdd (fun _ : Fin ((∏ j, counts j) / R) ↦
        MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j)))
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (counts j / repair j) ↦
        MMObj K (a j) (b j) (c j)))) := by
  have hlocal (j : Fin k) : counts j ≤ (2 * repair j) * (counts j / repair j) := by
    have hmod := Nat.mod_lt (counts j) (hpos j)
    have hdiv := Nat.div_pos (henough j) (hpos j)
    have heq := Nat.mod_add_div (counts j) (repair j)
    nlinarith
  have hprod : (∏ j, counts j) ≤ R * ∏ j, counts j / repair j := by
    calc
      _ ≤ ∏ j, (2 * repair j) * (counts j / repair j) :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun j _ ↦ hlocal j)
      _ = (∏ j, 2 * repair j) * ∏ j, counts j / repair j := Finset.prod_mul_distrib
      _ ≤ _ := Nat.mul_le_mul_right _ hR
  have hcap : (∏ j, counts j) / R ≤ ∏ j, counts j / repair j :=
    Nat.div_le_of_le_mul hprod
  exact (mme_bigAdd_prefix_restrict (by decide : 1 < 3) hcap
    (fun _ ↦ MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j))).trans
      (product_of_sums a b c (fun j ↦ counts j / repair j)).2
