-- Prove2me | solution 1 for MarkovMixing.coupon_tail
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:29:43.361414+00:00
-- url     : https://prove2.me/submissions/5194012e-8766-4bef-bebd-663243b06e65

import Definitions.Def_mm_classical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators
open MarkovMixing

theorem solution (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) :
    couponMissProb n ⌈(n : ℝ) * Real.log n + c * n⌉₊ ≤ Real.exp (-c) := by
  classical
  set t : ℕ := ⌈(n : ℝ) * Real.log n + c * n⌉₊ with ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- (1) union bound on the non-surjective functions
  have hsub : (Finset.univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d)
      ⊆ Finset.univ.biUnion
        (fun i : Fin n => Finset.univ.filter fun d : Fin t → Fin n => ∀ s, d s ≠ i) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    rw [Function.Surjective] at hd
    push Not at hd
    obtain ⟨i, hi⟩ := hd
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨i, fun s => hi s⟩
  have hcardA : ∀ i : Fin n,
      (Finset.univ.filter fun d : Fin t → Fin n => ∀ s, d s ≠ i).card = (n - 1) ^ t := by
    intro i
    have hset : (Finset.univ.filter fun d : Fin t → Fin n => ∀ s, d s ≠ i)
        = Fintype.piFinset (fun _ : Fin t => Finset.univ.erase i) := by
      ext d
      simp [Fintype.mem_piFinset, Finset.mem_erase]
    rw [hset, Fintype.card_piFinset]
    simp [Finset.card_erase_of_mem, Finset.card_univ]
  have hcard : (Finset.univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card
      ≤ n * (n - 1) ^ t := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    rw [Finset.sum_congr rfl (fun i _ => hcardA i)]
    simp [Finset.sum_const, Finset.card_univ]
  -- (2) pass to reals
  have hpow : (0 : ℝ) < (n : ℝ) ^ t := by positivity
  have hnum : ((Finset.univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card : ℝ)
      ≤ (n : ℝ) * ((n : ℝ) - 1) ^ t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcard
    refine le_trans h ?_
    have hc1 : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      push_cast [Nat.cast_sub hn]
      ring
    push_cast [hc1]
    exact le_of_eq rfl
  have hstep1 : couponMissProb n t ≤ (n : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) ^ t := by
    unfold couponMissProb
    rw [div_le_iff₀ hpow]
    calc ((Finset.univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card : ℝ)
        ≤ (n : ℝ) * ((n : ℝ) - 1) ^ t := hnum
      _ = (n : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) ^ t * (n : ℝ) ^ t := by
          rw [div_pow]
          field_simp
  -- (3) 1 - 1/n ≤ exp (-1/n)
  have hb : ((n : ℝ) - 1) / (n : ℝ) = 1 + (-1 / (n : ℝ)) := by
    field_simp
    ring
  have hbnn : (0 : ℝ) ≤ ((n : ℝ) - 1) / (n : ℝ) := by
    apply div_nonneg _ (le_of_lt hnR)
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hexp1 : ((n : ℝ) - 1) / (n : ℝ) ≤ Real.exp (-1 / (n : ℝ)) := by
    rw [hb, add_comm]
    exact Real.add_one_le_exp _
  have hstep2 : (((n : ℝ) - 1) / (n : ℝ)) ^ t ≤ Real.exp (-(t : ℝ) / (n : ℝ)) := by
    calc (((n : ℝ) - 1) / (n : ℝ)) ^ t ≤ (Real.exp (-1 / (n : ℝ))) ^ t :=
          pow_le_pow_left₀ hbnn hexp1 t
      _ = Real.exp (-(t : ℝ) / (n : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  -- (4) the choice of `t`
  have hT : (n : ℝ) * Real.log n + c * n ≤ (t : ℝ) := Nat.le_ceil _
  have hfinal : (n : ℝ) * Real.exp (-(t : ℝ) / (n : ℝ)) ≤ Real.exp (-c) := by
    have hlog : Real.log n + -(t : ℝ) / (n : ℝ) ≤ -c := by
      rw [div_le_iff₀ hnR] at *
      have h2 : Real.log n * (n : ℝ) + c * n ≤ (t : ℝ) := by
        calc Real.log n * (n : ℝ) + c * n = (n : ℝ) * Real.log n + c * n := by ring
          _ ≤ (t : ℝ) := hT
      have : Real.log n + -(t : ℝ) / (n : ℝ) ≤ -c := by
        rw [← sub_nonneg]
        have hdiv : (t : ℝ) / (n : ℝ) ≥ Real.log n + c := by
          rw [ge_iff_le, le_div_iff₀ hnR]
          linarith
        have : -(t : ℝ) / (n : ℝ) = -((t : ℝ) / (n : ℝ)) := by ring
        rw [this]
        linarith
      exact this
    calc (n : ℝ) * Real.exp (-(t : ℝ) / (n : ℝ))
        = Real.exp (Real.log n) * Real.exp (-(t : ℝ) / (n : ℝ)) := by
          rw [Real.exp_log hnR]
      _ = Real.exp (Real.log n + -(t : ℝ) / (n : ℝ)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-c) := Real.exp_le_exp.mpr hlog
  calc couponMissProb n t ≤ (n : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) ^ t := hstep1
    _ ≤ (n : ℝ) * Real.exp (-(t : ℝ) / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hstep2 (le_of_lt hnR)
    _ ≤ Real.exp (-c) := hfinal
