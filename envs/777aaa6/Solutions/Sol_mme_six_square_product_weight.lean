-- Prove2me | solution 1 for mme_six_square_product_weight
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:50:25.889129+00:00
-- url     : https://prove2.me/submissions/57239525-cc96-40ea-a438-940f44d08167

import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators
universe u
set_option autoImplicit false

private theorem kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem kronFin_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ i, TensorObj.Restrict (X i) (Y i)) →
      TensorObj.Restrict (TensorObj.kronFin n X) (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y h
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun i ↦ X i.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun i ↦ Y i.succ)))
      exact kron_restrict_for_tau_product hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


/-- Finite six-symmetric square-matrix extractions combine without a loss in
exponential weight. -/
theorem solution {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (M : Fin n → ℕ) (rate : Fin n → ℝ) (tau : ℝ)
    (hextract : ∀ i, TensorObj.Restrict (MMObj K (M i) (M i) (M i))
      (sixSymmetrization (T i)))
    (hweight : ∀ i, Real.exp (rate i) ≤ ((M i * M i * M i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict (MMObj K (∏ i, M i) (∏ i, M i) (∏ i, M i))
      (sixSymmetrization (TensorObj.kronFin n T)) ∧
    Real.exp (∑ i, rate i) ≤
      ((((∏ i, M i) * (∏ i, M i) * (∏ i, M i) : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (mme_kronFin_MMObj_iso (K := K) n M M M).2.trans
      ((kronFin_restrict_for_tau_product (by decide) n _ _ hextract).trans
        (mme_sixSymmetrization_kronFin_isomorphic T).1)
  · rw [Real.exp_sum]
    have hprod := Finset.prod_le_prod
      (fun i (_ : i ∈ Finset.univ) ↦ (Real.exp_pos (rate i)).le)
      (fun i (_ : i ∈ Finset.univ) ↦ hweight i)
    calc
      ∏ i, Real.exp (rate i) ≤ ∏ i, ((M i * M i * M i : ℕ) : ℝ) ^ tau := hprod
      _ = (∏ i, ((M i * M i * M i : ℕ) : ℝ)) ^ tau := by
        rw [Real.finset_prod_rpow]
        intro i _
        positivity
      _ = _ := by
        simp only [Nat.cast_mul, Nat.cast_prod, Finset.prod_mul_distrib]


#print axioms solution
