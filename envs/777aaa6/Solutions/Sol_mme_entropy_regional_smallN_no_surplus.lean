-- Prove2me | solution 1 for mme_entropy_regional_smallN_no_surplus
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-19T20:43:47.606877+00:00
-- url     : https://prove2.me/submissions/275c520d-0efd-4b61-9205-ff6993a4886b

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_entropy_regional_smallN_outputs_le_one
import Theorems.Thm_mme_boundary_dims_le_seven_pow
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open MME MME.ProfiledCW MME.RegionRealization

set_option autoImplicit false

theorem solution : forall (N ell : Nat) (P : MME.ProfiledCW.Predicate N) (D : EntropyRecipe N ell P), N <= 2 -> D.inputs = 1 -> ¬(((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by
  have dims_le : forall {N ell : Nat} {P : MME.ProfiledCW.Predicate N} (D : EntropyRecipe N ell P), D.a * D.b * D.c <= 7 ^ N := by
    intro N ell P D
    induction D with
    | boundary data =>
      exact mme_boundary_dims_le_seven_pow _ _ _ data
    | descend level_decreases types copies steps enough inside cover next ih =>
      show next.a * next.b * next.c <= _
      exact ih
    | partition size positions Q inside children ih =>
      have he := Fintype.card_congr positions
      rw [Fintype.card_fin, Fintype.card_sigma] at he
      simp only [Fintype.card_fin] at he
      have hEq : (EntropyRecipe.partition size positions Q inside children).a *
          (EntropyRecipe.partition size positions Q inside children).b *
          (EntropyRecipe.partition size positions Q inside children).c =
          ∏ j, ((children j).a * (children j).b * (children j).c) := by
        simp only [EntropyRecipe.a, EntropyRecipe.b, EntropyRecipe.c, EntropyRecipe.dims, ← Finset.prod_mul_distrib]
      rw [hEq]
      calc ∏ j, ((children j).a * (children j).b * (children j).c)
          ≤ ∏ j, 7 ^ (size j) :=
            Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => ih i)
        _ = 7 ^ (∑ j, size j) := by
            rw [Finset.prod_pow_eq_pow_sum]
        _ = _ := by rw [he]
    | rotate child ih =>
      show child.c * child.a * child.b <= _
      calc child.c * child.a * child.b = child.a * child.b * child.c := by ring
        _ <= _ := ih
    | swap child ih =>
      show child.c * child.b * child.a <= _
      calc child.c * child.b * child.a = child.a * child.b * child.c := by ring
        _ <= _ := ih
  intro N ell P D hN hIn hSur
  have hOut : D.outputs <= 1 := mme_entropy_regional_smallN_outputs_le_one N ell P D hN hIn
  have hDims : D.a * D.b * D.c <= 7 ^ N := dims_le D
  have hLHS : (((D.inputs * 7 ^ N : Nat) : Real) = (((7 ^ N : Nat)) : Real)) := by
    rw [hIn, one_mul]
  rw [hLHS] at hSur
  have hTau_nonneg : (0 : Real) <= (3952233 : Real) / 5000000 := by norm_num
  have hTau_le_one : ((3952233 : Real) / 5000000) <= 1 := by norm_num
  have habc_le : (((D.a * D.b * D.c : Nat)) : Real) <= (((7 ^ N : Nat)) : Real) := by
    exact_mod_cast hDims
  have h7N_ge_one : (1 : Real) <= (((7 ^ N : Nat)) : Real) := by
    have h1 : 1 <= 7 ^ N := Nat.one_le_pow N 7 (by norm_num)
    exact_mod_cast h1
  have hOut_eq : D.outputs = 0 ∨ D.outputs = 1 := by omega
  rcases hOut_eq with h0 | h1
  · rw [h0, Nat.cast_zero, zero_mul] at hSur
    exact absurd hSur (not_lt_of_ge (Nat.cast_nonneg _))
  · rw [h1, Nat.cast_one, one_mul] at hSur
    have hbase_nn : (0 : Real) <= (((D.a * D.b * D.c : Nat)) : Real) := Nat.cast_nonneg _
    have hstep1 : ((((D.a * D.b * D.c : Nat)) : Real) ^ ((3952233 : Real) / 5000000))
        <= ((((7 ^ N : Nat)) : Real) ^ ((3952233 : Real) / 5000000)) :=
      Real.rpow_le_rpow hbase_nn habc_le hTau_nonneg
    have hstep2 : ((((7 ^ N : Nat)) : Real) ^ ((3952233 : Real) / 5000000))
        <= ((((7 ^ N : Nat)) : Real)) := by
      have h := Real.rpow_le_rpow_of_exponent_le h7N_ge_one hTau_le_one
      rwa [Real.rpow_one] at h
    have hle : ((((D.a * D.b * D.c : Nat)) : Real) ^ ((3952233 : Real) / 5000000))
        <= ((((7 ^ N : Nat)) : Real)) := le_trans hstep1 hstep2
    exact absurd (lt_of_lt_of_le hSur hle) (lt_irrefl _)
