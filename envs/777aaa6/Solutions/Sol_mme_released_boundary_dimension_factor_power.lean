-- Prove2me | solution 1 for mme_released_boundary_dimension_factor_power
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:00.618985+00:00
-- url     : https://prove2.me/submissions/33a1e685-f660-4b86-8782-507335e39cb0

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Vandermonde
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false


open Nat in
section


private theorem choose_mul_choose_le_add (a b c d : ℕ) :
    a.choose c * b.choose d ≤ (a + b).choose (c + d) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ ↦ a.choose ij.1 * b.choose ij.2)
    (fun _ _ ↦ Nat.zero_le _) (a := (c, d)) (Finset.mem_antidiagonal.mpr rfl)

private theorem prod_choose_le_choose_sum {S : Type*} (s : Finset S) (x y : S → ℕ) :
    ∏ i ∈ s, (x i).choose (y i) ≤ (∑ i ∈ s, x i).choose (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    calc (x i).choose (y i) * ∏ j ∈ s, (x j).choose (y j)
        ≤ (x i).choose (y i) * (∑ j ∈ s, x j).choose (∑ j ∈ s, y j) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ _ := choose_mul_choose_le_add _ _ _ _

private theorem multinomial_mul_le_add {S : Type*} (s : Finset S) (f g : S → ℕ) :
    Nat.multinomial s f * Nat.multinomial s g ≤ Nat.multinomial s (f + g) := by
  have hpos : 0 < ∏ i ∈ s, (f i + g i)! := Finset.prod_pos (fun i _ ↦ Nat.factorial_pos _)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have hfg := Nat.multinomial_spec s (f + g)
  simp only [Pi.add_apply] at hfg
  rw [hfg, Finset.sum_add_distrib]
  have hsplit : ∏ i ∈ s, (f i + g i)! =
      (∏ i ∈ s, (f i)!) * (∏ i ∈ s, (g i)!) * ∏ i ∈ s, (f i + g i).choose (f i) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ ↦ ?_)
    have := Nat.add_choose_mul_factorial_mul_factorial (g i) (f i)
    rw [add_comm (g i) (f i)] at this
    rw [← this]; ring
  rw [hsplit]
  have hf := Nat.multinomial_spec s f
  have hg := Nat.multinomial_spec s g
  have key := prod_choose_le_choose_sum s (fun i ↦ f i + g i) f
  simp only [Finset.sum_add_distrib] at key
  have hbin := Nat.add_choose_mul_factorial_mul_factorial (∑ i ∈ s, g i) (∑ i ∈ s, f i)
  rw [add_comm (∑ i ∈ s, g i)] at hbin
  calc (∏ i ∈ s, (f i)!) * (∏ i ∈ s, (g i)!) * (∏ i ∈ s, (f i + g i).choose (f i)) *
        (Nat.multinomial s f * Nat.multinomial s g)
      = ((∏ i ∈ s, (f i)!) * Nat.multinomial s f) * ((∏ i ∈ s, (g i)!) * Nat.multinomial s g) *
          ∏ i ∈ s, (f i + g i).choose (f i) := by ring
    _ = (∑ i ∈ s, f i).factorial * (∑ i ∈ s, g i).factorial * ∏ i ∈ s, (f i + g i).choose (f i) := by rw [hf, hg]
    _ ≤ (∑ i ∈ s, f i).factorial * (∑ i ∈ s, g i).factorial *
          (∑ i ∈ s, f i + ∑ i ∈ s, g i).choose (∑ i ∈ s, f i) := Nat.mul_le_mul_left _ key
    _ = (∑ i ∈ s, f i + ∑ i ∈ s, g i)! := by rw [← hbin]; ring

private theorem multinomial_pow_le_smul {S : Type*} (s : Finset S) (f : S → ℕ) (k : ℕ) :
    Nat.multinomial s f ^ k ≤ Nat.multinomial s (fun i ↦ k * f i) := by
  induction k with
  | zero => rw [pow_zero]; exact Nat.multinomial_pos _ _
  | succ k ih =>
    rw [pow_succ]
    calc Nat.multinomial s f ^ k * Nat.multinomial s f
        ≤ Nat.multinomial s (fun i ↦ k * f i) * Nat.multinomial s f := Nat.mul_le_mul_right _ ih
      _ ≤ Nat.multinomial s ((fun i ↦ k * f i) + f) := multinomial_mul_le_add _ _ _
      _ = _ := by congr 1; funext i; simp only [Pi.add_apply]; ring

end

theorem solution (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) :
    1 ≤ (∏ c : Fin zCells,
          ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
          5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s)) ∧
    (∏ c : Fin zCells,
          ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
          5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s)) ^ k ≤
      ∏ c : Fin zCells,
          ((Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c}).factorial /
            ∏ s, (zCountAt k c s).factorial) *
          5 ^ (∑ s, zCountAt k c s * Boundary.ones s) := by
  have hscale : ∀ c s, zCountAt k c s = k * zCountAt 1 c s := by
    intro c s; simp [zCountAt, scaledWords]
  have hM : ∀ c : Fin zCells,
      (∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial =
        Nat.multinomial Finset.univ (fun s ↦ zCountAt 1 c s) := fun c ↦ rfl
  have hMk : ∀ c : Fin zCells,
      (Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c}).factorial /
          ∏ s, (zCountAt k c s).factorial =
        Nat.multinomial Finset.univ (fun s ↦ k * zCountAt 1 c s) := by
    intro c
    rw [← zCount_total k hk a c]
    simp only [hscale]
    rfl
  have hE : ∀ c : Fin zCells, ∑ s, zCountAt k c s * Boundary.ones s =
      k * ∑ s, zCountAt 1 c s * Boundary.ones s := by
    intro c; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [hscale]; ring
  simp only [hM, hMk, hE]
  refine ⟨?_, ?_⟩
  · exact Finset.prod_pos (fun c _ ↦ Nat.mul_pos (Nat.multinomial_pos _ _) (by positivity))
  · rw [← Finset.prod_pow]
    refine Finset.prod_le_prod' (fun c _ ↦ ?_)
    rw [mul_pow, ← pow_mul, mul_comm (∑ s, zCountAt 1 c s * Boundary.ones s) k]
    exact Nat.mul_le_mul_right _ (multinomial_pow_le_smul _ _ _)

