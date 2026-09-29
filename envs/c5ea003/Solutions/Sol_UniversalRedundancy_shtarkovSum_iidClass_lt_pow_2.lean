-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_iidClass_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:46:14.359396+00:00
-- url     : https://prove2.me/submissions/293b6372-7fee-4e64-a24e-20b0a7fac66a

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (hA : 2 ≤ Fintype.card A) :
    ∀ n : ℕ, 2 ≤ n → (iidClass A n).shtarkovSum < (Fintype.card A : ℝ) ^ n := by
  intro n hn
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  have hb : ∀ (θ : Simplex A) x, (iidClass A n).prob θ x ≤ 1 := by
    intro θ x
    rw [← (iidClass A n).sum_one θ]
    exact Finset.single_le_sum (f := fun y => (iidClass A n).prob θ y)
      (fun z _ => (iidClass A n).nonneg θ z) (Finset.mem_univ x)
  have hml1 : ∀ x, (iidClass A n).maxLik x ≤ 1 := fun x => ciSup_le (fun θ => hb θ x)
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let x : Fin n → A := fun i => if i.val = 0 then a else b
  have hx0 : x i0 = a := by simp [x, i0]
  have hx1 : x i1 = b := by simp [x, i1]
  have hθle : ∀ (θ : Simplex A) c, θ.1 c ≤ 1 := by
    intro θ c
    exact le_of_le_of_eq
      (Finset.single_le_sum (f := fun c => θ.1 c) (fun c _ => θ.2.1 c) (Finset.mem_univ c)) θ.2.2
  have hxml : (iidClass A n).maxLik x ≤ 1 / 4 := by
    refine ciSup_le (fun θ => ?_)
    show ∏ i, θ.1 (x i) ≤ 1 / 4
    have hsplit := Finset.prod_sdiff (Finset.subset_univ ({i0, i1} : Finset (Fin n))) (f := fun i => θ.1 (x i))
    have hrest : ∏ i ∈ Finset.univ \ {i0, i1}, θ.1 (x i) ≤ 1 :=
      Finset.prod_le_one (fun i _ => θ.2.1 _) (fun i _ => hθle θ _)
    have hpair : ∏ i ∈ ({i0, i1} : Finset (Fin n)), θ.1 (x i) = θ.1 a * θ.1 b := by
      rw [Finset.prod_pair hi, hx0, hx1]
    have hsum : θ.1 a + θ.1 b ≤ 1 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({a, b} : Finset A))
        (fun c _ _ => θ.2.1 c) (f := fun c => θ.1 c)
      rw [Finset.sum_pair hab] at this
      exact le_of_le_of_eq this θ.2.2
    have ha0 := θ.2.1 a
    have hb0 := θ.2.1 b
    have hpair_le : θ.1 a * θ.1 b ≤ 1 / 4 := by nlinarith [sq_nonneg (θ.1 a - θ.1 b)]
    have hrest0 : 0 ≤ ∏ i ∈ Finset.univ \ {i0, i1}, θ.1 (x i) := Finset.prod_nonneg (fun i _ => θ.2.1 _)
    rw [← hsplit, hpair]
    nlinarith [mul_nonneg ha0 hb0]
  have hcard : (Fintype.card (Fin n → A) : ℝ) = (Fintype.card A : ℝ) ^ n := by
    simp
  unfold SourceClass.shtarkovSum
  calc ∑ y, (iidClass A n).maxLik y < ∑ _y : Fin n → A, (1 : ℝ) :=
        Finset.sum_lt_sum (fun y _ => hml1 y) ⟨x, Finset.mem_univ _, by linarith⟩
    _ = (Fintype.card A : ℝ) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
