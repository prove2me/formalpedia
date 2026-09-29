-- Prove2me | solution 1 for mme_CW_kronPow_restrict_mono
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:38:59.470034+00:00
-- url     : https://prove2.me/submissions/ef86fa80-3b10-4ead-9f4c-cf1ad5f71f39

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_rank_bridge

open MME PiTensorProduct
universe u
set_option autoImplicit false

namespace CWPowerPadding
noncomputable def boundaryProjection (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3, CWSpace K q i →ₗ[K] K
  | ⟨0, _⟩ => LinearMap.proj ⟨0, by omega⟩
  | ⟨1, _⟩ => LinearMap.proj ⟨0, by omega⟩
  | ⟨2, _⟩ => LinearMap.proj ⟨q + 1, by omega⟩

private theorem monomial_zero {K : Type u} [Field K] (q : ℕ)
    (a b c : Fin (q + 2)) (h : a ≠ 0 ∨ b ≠ 0 ∨ c.val ≠ q + 1) :
    PiTensorProduct.map (boundaryProjection K q) (CWMonom K q a b c) = 0 := by
  rw [CWMonom, PiTensorProduct.map_tprod]
  rcases h with ha | hb | hc
  · apply (PiTensorProduct.tprod K).map_coord_zero 0
    change (Pi.single a 1 : Fin (q + 2) → K) 0 = 0
    exact Pi.single_eq_of_ne (Ne.symm ha) 1
  · apply (PiTensorProduct.tprod K).map_coord_zero 1
    change (Pi.single b 1 : Fin (q + 2) → K) 0 = 0
    exact Pi.single_eq_of_ne (Ne.symm hb) 1
  · apply (PiTensorProduct.tprod K).map_coord_zero 2
    have hn : c ≠ (⟨q + 1, by omega⟩ : Fin (q + 2)) := by
      intro he; exact hc (congrArg Fin.val he)
    change (Pi.single c 1 : Fin (q + 2) → K) ⟨q + 1, by omega⟩ = 0
    exact Pi.single_eq_of_ne (Ne.symm hn) 1

theorem one_restricts_CW (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict TensorObj.oneObj (CWObj K q) := by
  classical
  refine ⟨boundaryProjection K q, ?_⟩
  change PiTensorProduct.map (boundaryProjection K q) (CWTensor K q) = _
  unfold CWTensor
  rw [map_add, map_add, map_add, map_sum]
  have hsum : ∑ i : Fin q, PiTensorProduct.map (boundaryProjection K q)
      (CWMonom K q ⟨0, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ +
       CWMonom K q ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩ ⟨i.val + 1, by omega⟩ +
       CWMonom K q ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [map_add, map_add]
    have hi : (⟨i.val + 1, by omega⟩ : Fin (q + 2)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
    rw [monomial_zero q _ _ _ (Or.inr (Or.inl hi)),
      monomial_zero q _ _ _ (Or.inl hi), monomial_zero q _ _ _ (Or.inl hi)]
    simp
  rw [hsum]
  have ht : (⟨q + 1, by omega⟩ : Fin (q + 2)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
  rw [monomial_zero q _ _ _ (Or.inr (Or.inl ht)),
    monomial_zero q _ _ _ (Or.inl ht), zero_add, add_zero, add_zero]
  rw [CWMonom, PiTensorProduct.map_tprod]
  congr 1
  funext i
  fin_cases i
  · change (Pi.single (0 : Fin (q + 2)) 1 : Fin (q + 2) → K) 0 = 1
    exact Pi.single_eq_same 0 1
  · change (Pi.single (0 : Fin (q + 2)) 1 : Fin (q + 2) → K) 0 = 1
    exact Pi.single_eq_same 0 1
  · change (Pi.single (⟨q + 1, by omega⟩ : Fin (q + 2)) 1 : Fin (q + 2) → K)
      ⟨q + 1, by omega⟩ = 1
    exact Pi.single_eq_same _ 1

end CWPowerPadding

/-- Extra elementary CW factors can be removed by boundary-coordinate projections. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) {m n : ℕ} (h : m ≤ n) :
    TensorObj.Restrict ((CWObj K q).kronPow m) ((CWObj K q).kronPow n) := by
  let S := TensorQ.tensorStrassen K 3 (by omega)
  let x := TensorQ.toQ (CWObj K q)
  have hx : TensorQ.le 1 x := CWPowerPadding.one_restricts_CW K q
  have hp : ∀ k, TensorQ.le (x ^ k) (x ^ (k + 1)) := by
    intro k
    have hh := S.mul_right 1 x hx (x ^ k)
    simpa only [one_mul, ← pow_succ', Nat.add_comm] using hh
  have hm : TensorQ.le (x ^ m) (x ^ n) := by
    induction h with
    | refl => exact TensorQ.le_refl _
    | @step n h ih => exact TensorQ.le_trans _ _ _ ih (hp n)
  apply TensorQ.le_toQ _ _ |>.1
  simpa only [TensorQ.toQ_kronPow] using hm

#print axioms solution
