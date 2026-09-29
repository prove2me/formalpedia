-- Prove2me | solution 1 for mme_Ctensor_three_unequal_outer_families_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:49:08.260134+00:00
-- url     : https://prove2.me/submissions/b4aa9574-8b50-4dbd-9c61-f914485d0fed

import Theorems.Thm_mme_Ctensor_three_unequal_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_rank_bridge
import Mathlib.Data.Fintype.Card

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem perm_bigAdd_toQ
    {K : Type u} [Field K] {A : ℕ}
    (sigma : Equiv.Perm (Fin 3)) (S : Fin A → TensorObj K 3) :
    TensorQ.toQ (TensorObj.permObj sigma (TensorObj.bigAdd S)) =
      ∑ a, TensorQ.toQ (TensorObj.permObj sigma (S a)) := by
  calc
    _ = TensorQ.permAut sigma (TensorQ.toQ (TensorObj.bigAdd S)) := by
      rw [TensorQ.permAut_toQ]
    _ = TensorQ.permAut sigma (∑ a, TensorQ.toQ (S a)) := by
      rw [TensorQ.toQ_bigAdd]
    _ = _ := by simp

/-- The checked finite outer distribution proof generalized from one family
to three independently indexed literal families; no power distribution. -/
private theorem unequal_outer_distribution
    {K : Type u} [Field K] {A0 A1 A2 : ℕ}
    (S0 : Fin A0 → TensorObj K 3)
    (S1 : Fin A1 → TensorObj K 3)
    (S2 : Fin A2 → TensorObj K 3) :
    let I := Fin A0 × Fin A1 × Fin A2
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
      let p := e.symm j
      threeStarCyclicProduct (S0 p.1) (S1 p.2.1) (S2 p.2.2)
    TensorObj.Restrict (TensorObj.bigAdd block)
      (threeStarCyclicProduct
        (TensorObj.bigAdd S0) (TensorObj.bigAdd S1) (TensorObj.bigAdd S2)) := by
  classical
  dsimp only
  let I := Fin A0 × Fin A1 × Fin A2
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct (S0 p.1) (S1 p.2.1) (S2 p.2.2)
  apply ((TensorQ.toQ_eq_iff).mp ?_).1
  rw [TensorQ.toQ_bigAdd, threeStarCyclicProduct,
    TensorQ.toQ_kron, TensorQ.toQ_kron, TensorQ.toQ_bigAdd,
    perm_bigAdd_toQ, perm_bigAdd_toQ]
  calc
    (∑ j : Fin (Fintype.card I), TensorQ.toQ (block j)) =
        ∑ p : I, TensorQ.toQ
          (threeStarCyclicProduct (S0 p.1) (S1 p.2.1) (S2 p.2.2)) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      simp only [block, Equiv.symm_apply_apply]
    _ = ∑ a : Fin A0, ∑ b : Fin A1, ∑ c : Fin A2,
        TensorQ.toQ (S0 a) *
          (TensorQ.toQ (TensorObj.permObj cyclicPerm (S1 b)) *
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (S2 c))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro c _hc
      simp only [threeStarCyclicProduct, TensorQ.toQ_kron]
    _ = (∑ a : Fin A0, TensorQ.toQ (S0 a)) *
        ((∑ b : Fin A1,
            TensorQ.toQ (TensorObj.permObj cyclicPerm (S1 b))) *
          (∑ c : Fin A2,
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (S2 c)))) := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

/-- Literal unequal outer families add after the three directional consumers
have been combined. Each outer triple receives the same strict value bound. -/
theorem solution
    {K : Type u} [Field K]
    {A0 A1 A2 H0 H1 H2 v0 v1 v2 : ℕ}
    (S0 : Fin A0 → TensorObj K 3)
    (S1 : Fin A1 → TensorObj K 3)
    (S2 : Fin A2 → TensorObj K 3)
    (cert0 : ∀ a, CTensorOneHOneCertificate (S0 a) H0 v0)
    (cert1 : ∀ a, CTensorOneHOneCertificate (S1 a) H1 v1)
    (cert2 : ∀ a, CTensorOneHOneCertificate (S2 a) H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2)
    (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < ((A0 * A1 * A2 : ℕ) : ℝ) *
      ((min (H0 * H1) (min (H0 * H2) (H1 * H2)) : ℕ) : ℝ) *
      (((v0 * v1 * v2 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast
      (threeStarCyclicProduct
        (TensorObj.bigAdd S0) (TensorObj.bigAdd S1) (TensorObj.bigAdd S2)) tau V := by
  classical
  let I := Fin A0 × Fin A1 × Fin A2
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct (S0 p.1) (S1 p.2.1) (S2 p.2.2)
  let B : ℝ := ((min (H0 * H1) (min (H0 * H2) (H1 * H2)) : ℕ) : ℝ) *
    (((v0 * v1 * v2 : ℕ) : ℝ) ^ tau)
  have hB : 0 ≤ B :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) tau)
  have hblocks : ∀ j : Fin (Fintype.card I), ∀ W : ℝ,
      0 ≤ W → W < B → HasTauValueAtLeast (block j) tau W := by
    intro j W hW hWB
    exact mme_Ctensor_three_unequal_cyclic_value_below
      (cert0 (e.symm j).1) (cert1 (e.symm j).2.1) (cert2 (e.symm j).2.2)
      h0 h1 h2 hv0 hv1 hv2 tau W hW hWB
  have hcard : Fintype.card I = A0 * A1 * A2 := by
    simp [I, Nat.mul_assoc]
  apply mme_HasTauValueAtLeast_mono_restrict (unequal_outer_distribution S0 S1 S2)
  apply mme_HasTauValueAtLeast_bigAdd_uniform_strict block tau B hB hblocks V hV
  simpa only [hcard, B, mul_assoc] using hVlt

