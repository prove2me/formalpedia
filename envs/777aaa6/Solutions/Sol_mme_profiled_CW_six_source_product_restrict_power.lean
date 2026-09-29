-- Prove2me | solution 1 for mme_profiled_CW_six_source_product_restrict_power
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:16.607845+00:00
-- url     : https://prove2.me/submissions/2e34aafe-c048-424a-81f2-372f671278db

import Theorems.Thm_mme_profiled_CW_repeated_six_restrict_power
import Theorems.Thm_mme_toQ_kronFin

open MME MME.TensorObj BigOperators
universe u
set_option autoImplicit false

private theorem kron_restrict
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

private theorem kronFin_restrict
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
      exact kron_restrict hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

/-- The six profiled source families restrict to a single family of elementary
CW powers, with the exact product of sixth-power input multiplicities. -/
theorem solution
    {K : Type u} [Field K] (N : ℕ) (inputs : Fin 6 → ℕ)
    (P : Fin 6 → ProfiledCW.Predicate (4 * N)) :
    Restrict
      (kronFin 6 (fun owner => sixSymmetrization
        (bigAdd (fun _ : Fin (inputs owner) => ProfiledCW.tensor K (P owner)))))
      (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
        (CWObj K 5).kronPow (144 * N))) := by
  let Y := fun owner : Fin 6 =>
    bigAdd (fun _ : Fin (inputs owner ^ 6) => (CWObj K 5).kronPow (24 * N))
  have h := kronFin_restrict (K := K) (by norm_num) 6 _ Y
    (fun owner => mme_profiled_CW_repeated_six_restrict_power N (inputs owner) (P owner))
  have hiso : TensorObj.Isomorphic (kronFin 6 Y)
      (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
        (CWObj K 5).kronPow (144 * N))) := by
    apply TensorQ.toQ_eq_iff.1
    simp only [Y, mme_toQ_kronFin, TensorQ.toQ_bigAdd, TensorQ.toQ_kronPow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.prod_mul_distrib, Finset.prod_const]
    rw [← Nat.cast_prod, ← pow_mul]
    congr 2
    ring
  exact h.trans hiso.1


#print axioms solution
