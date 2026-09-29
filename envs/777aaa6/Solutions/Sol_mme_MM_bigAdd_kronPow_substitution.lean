-- Prove2me | solution 1 for mme_MM_bigAdd_kronPow_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:17:04.670258+00:00
-- url     : https://prove2.me/submissions/b1c4dacf-27e4-4309-b4a0-419c46b58356

import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators

universe u

namespace MMBigAddKronPowSubstitution

theorem prod_MMq
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {kc : ℕ} (xc yc zc : Fin kc → ℕ)
    (w : ι → Fin kc) :
    (∏ t, MMq K (xc (w t)) (yc (w t)) (zc (w t))) =
      MMq K (∏ t, xc (w t)) (∏ t, yc (w t)) (∏ t, zc (w t)) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using (MMq_one (K := K)).symm
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, ih, MMq_mul]
      simp only [Finset.prod_insert hi]

theorem rpow_prod_natCast
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (tau : ℝ) :
    (((∏ i, f i : ℕ) : ℝ) ^ tau) =
      ∏ i, (((f i : ℕ) : ℝ) ^ tau) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Nat.cast_mul,
        Real.mul_rpow (by positivity) (by positivity), ih]
      simp only [Finset.prod_insert hi]

theorem volume_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {kc : ℕ} (a b c : ℕ) (xc yc zc : Fin kc → ℕ)
    (w : ι → Fin kc) :
    (a * ∏ t, xc (w t)) * (b * ∏ t, yc (w t)) *
        (c * ∏ t, zc (w t)) =
      (a * b * c) * ∏ t, (xc (w t) * yc (w t) * zc (w t)) := by
  classical
  rw [show (∏ t, (xc (w t) * yc (w t) * zc (w t))) =
      (∏ t, xc (w t)) * (∏ t, yc (w t)) * (∏ t, zc (w t)) by
        simp only [Finset.prod_mul_distrib]]
  ring

theorem term_weight_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {kc : ℕ} (tau : ℝ) (a b c : ℕ)
    (xc yc zc : Fin kc → ℕ) (w : ι → Fin kc) :
    ((((a * ∏ t, xc (w t)) * (b * ∏ t, yc (w t)) *
        (c * ∏ t, zc (w t)) : ℕ) : ℝ) ^ tau) =
      (((a * b * c : ℕ) : ℝ) ^ tau) *
        ∏ t, (((xc (w t) * yc (w t) * zc (w t) : ℕ) : ℝ) ^ tau) := by
  classical
  rw [volume_identity a b c xc yc zc w, Nat.cast_mul,
    Real.mul_rpow (by positivity) (by positivity),
    rpow_prod_natCast (fun t => xc (w t) * yc (w t) * zc (w t)) tau]

theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hd : 1 < d)
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict
      (TensorObj.kron X Y)
      (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  have hmul : P.le
      (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)
  exact hmul

end MMBigAddKronPowSubstitution

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 0 ≤ tau)
    (r s a b c kc : ℕ)
    (xc yc zc : Fin kc → ℕ)
    (X Y : TensorObj K 3)
    (hrestrict :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i))) X)
    (hpower : TensorObj.Isomorphic (X.kronPow r) Y) :
    ∃ (k : ℕ) (x y z : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
        (TensorObj.bigAdd
          (fun _ : Fin s => TensorObj.kron (MMObj K a b c) Y)) ∧
      (s : ℝ) *
          ((((a * b * c : ℕ) : ℝ) ^ tau) *
            (∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) ^ r) ≤
        ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  classical
  let I := Fin s × (Fin r → Fin kc)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let x : Fin (Fintype.card I) → ℕ := fun j =>
    a * ∏ t, xc ((e.symm j).2 t)
  let y : Fin (Fintype.card I) → ℕ := fun j =>
    b * ∏ t, yc ((e.symm j).2 t)
  let z : Fin (Fintype.card I) → ℕ := fun j =>
    c * ∏ t, zc ((e.symm j).2 t)
  refine ⟨Fintype.card I, x, y, z, ?_, ?_⟩
  · have hflat : TensorObj.Isomorphic
        (TensorObj.bigAdd (fun j => MMObj K (x j) (y j) (z j)))
        (TensorObj.bigAdd (fun _ : Fin s =>
          TensorObj.kron (MMObj K a b c)
            ((TensorObj.bigAdd
              (fun i => MMObj K (xc i) (yc i) (zc i))).kronPow r))) := by
      apply TensorQ.toQ_eq_iff.mp
      rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
      calc
        (∑ j : Fin (Fintype.card I),
            TensorQ.toQ (MMObj K (x j) (y j) (z j))) =
            ∑ p : I, TensorQ.toQ
              (MMObj K
                (a * ∏ t, xc (p.2 t))
                (b * ∏ t, yc (p.2 t))
                (c * ∏ t, zc (p.2 t))) := by
              symm
              apply Fintype.sum_equiv e
              intro p
              simp only [x, y, z, Equiv.symm_apply_apply]
        _ = ∑ _ : Fin s, TensorQ.toQ
              (TensorObj.kron (MMObj K a b c)
                ((TensorObj.bigAdd
                  (fun i => MMObj K (xc i) (yc i) (zc i))).kronPow r)) := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro j hj
              rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow,
                TensorQ.toQ_bigAdd]
              simp only [TensorQ.toQ]
              change (∑ w : Fin r → Fin kc,
                  MMq K
                    (a * ∏ t, xc (w t))
                    (b * ∏ t, yc (w t))
                    (c * ∏ t, zc (w t))) =
                MMq K a b c *
                  (∑ i : Fin kc, MMq K (xc i) (yc i) (zc i)) ^ r
              simp_rw [← MMq_mul]
              rw [← Finset.mul_sum, Fintype.sum_pow]
              congr 1
              apply Finset.sum_congr rfl
              intro w hw
              exact (MMBigAddKronPowSubstitution.prod_MMq xc yc zc w).symm
    have hpow_restrict := mme_restrict_kronPow hrestrict r
    have hAY : TensorObj.Restrict
        ((TensorObj.bigAdd
          (fun i => MMObj K (xc i) (yc i) (zc i))).kronPow r) Y :=
      TensorObj.Restrict.trans hpow_restrict hpower.1
    have hone : TensorObj.Restrict (MMObj K a b c) (MMObj K a b c) :=
      TensorObj.Restrict.refl _
    have hblock := MMBigAddKronPowSubstitution.kron_restrict
      (K := K) (d := 3) (by norm_num) hone hAY
    exact TensorObj.Restrict.trans hflat.1
      (mme_bigAdd_mono_restrict (fun _ : Fin s => hblock))
  · have hweight :
        (∑ j : Fin (Fintype.card I),
            (((x j * y j * z j : ℕ) : ℝ) ^ tau)) =
          (s : ℝ) *
            ((((a * b * c : ℕ) : ℝ) ^ tau) *
              (∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) ^ r) := by
      calc
        (∑ j : Fin (Fintype.card I),
            (((x j * y j * z j : ℕ) : ℝ) ^ tau)) =
            ∑ p : I,
              (((
                (a * ∏ t, xc (p.2 t)) *
                (b * ∏ t, yc (p.2 t)) *
                (c * ∏ t, zc (p.2 t)) : ℕ) : ℝ) ^ tau) := by
              symm
              apply Fintype.sum_equiv e
              intro p
              simp only [x, y, z, Equiv.symm_apply_apply]
        _ = ∑ _ : Fin s, ∑ w : Fin r → Fin kc,
              (((
                (a * ∏ t, xc (w t)) *
                (b * ∏ t, yc (w t)) *
                (c * ∏ t, zc (w t)) : ℕ) : ℝ) ^ tau) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ _ : Fin s,
              (((a * b * c : ℕ) : ℝ) ^ tau) *
                (∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) ^ r := by
              apply Finset.sum_congr rfl
              intro j hj
              simp_rw [MMBigAddKronPowSubstitution.term_weight_identity]
              rw [← Finset.mul_sum, Fintype.sum_pow]
        _ = (s : ℝ) *
              ((((a * b * c : ℕ) : ℝ) ^ tau) *
                (∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) ^ r) := by
              simp
    exact hweight.ge
