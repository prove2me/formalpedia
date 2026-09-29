-- Prove2me | solution 1 for ScaleSmoothness.dispersionBound_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:50:42.884947+00:00
-- url     : https://prove2.me/submissions/ee396834-0f97-456d-9829-faddd0ee6989

import Mathlib
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
-- NOTE: the mirror's `variable` line contributes a FIRST copy of `(a, Fact, hodd)` that the
-- API statement does not show, so the real target takes the triple twice.
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a₀ : ι → ℕ)
    [∀ i, Fact (a₀ i).Prime] (hodd₀ : ∀ i, a₀ i ≠ 2) (a : ι → ℕ)
    [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2) (hinj : Function.Injective a) :
    dispersionBound a ≤ 2 := by
  classical
  have ha3 : ∀ i, 3 ≤ a i := by
    intro i
    have h2 : 2 ≤ a i := (Fact.out : (a i).Prime).two_le
    have := hodd i
    omega
  -- the telescoping bound `∑_{n ≥ 3} 1/(n(n-1)) ≤ 1/2` (the `sum_inv_le_half` argument)
  have hinv : ∀ S : Finset ℕ, (∀ n ∈ S, 3 ≤ n) →
      ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) ≤ 1 / 2 := by
    intro S hS
    -- partial fractions: `1/(n(n-1)) = 1/(n-1) - 1/n`, the source of the telescoping
    have hsplit : ∀ x : ℚ, x + 2 ≠ 0 → x + 3 ≠ 0 →
        1 / ((x + 3) * ((x + 3) - 1)) = 1 / (x + 2) - 1 / (x + 3) := by
      intro x h2 h3
      rw [show x + 3 - 1 = x + 2 by ring, div_sub_div _ _ h2 h3,
        show 1 * (x + 3) - (x + 2) * 1 = 1 by ring, mul_comm (x + 2) (x + 3)]
    -- the telescoping identity `∑_{n=3}^{m+2} 1/(n(n-1)) = 1/2 - 1/(m+2)`
    have key : ∀ m : ℕ, ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        = 1 / 2 - 1 / ((m : ℚ) + 2) := by
      intro m
      induction m with
      | zero =>
        rw [Finset.Icc_eq_empty (by omega)]
        norm_num
      | succ k ih =>
        have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
        have h3 : (k : ℚ) + 3 ≠ 0 := by positivity
        have hc : ((k + 2 + 1 : ℕ) : ℚ) = (k : ℚ) + 3 := by push_cast; ring
        have hc2 : ((k + 1 : ℕ) : ℚ) + 2 = (k : ℚ) + 3 := by push_cast; ring
        rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih,
          hc, hsplit (k : ℚ) h2 h3, hc2]
        ring
    -- every element of `S` lies in `Icc 3 (sup S + 2)`
    set m := S.sup id with hm
    have hsub : S ⊆ Finset.Icc 3 (m + 2) := by
      intro n hn
      simp only [Finset.mem_Icc]
      refine ⟨hS n hn, ?_⟩
      have := Finset.le_sup (f := id) hn
      simp only [id] at this
      omega
    have hnn : ∀ n ∈ Finset.Icc 3 (m + 2), n ∉ S → (0 : ℚ) ≤ 1 / ((n : ℚ) * ((n : ℚ) - 1)) := by
      intro n hn _
      simp only [Finset.mem_Icc] at hn
      have h3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn.1
      apply div_nonneg zero_le_one
      nlinarith
    calc ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        ≤ ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
      _ = 1 / 2 - 1 / ((m : ℚ) + 2) := key m
      _ ≤ 1 / 2 := by
          have hpos : (0 : ℚ) < (m : ℚ) + 2 := by positivity
          have := one_div_pos.mpr hpos
          linarith
  -- transport it along the injective family `a`
  have hsum : ∑ i, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) ≤ 1 / 2 := by
    have himg : ∑ n ∈ Finset.univ.image a, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        = ∑ i, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) :=
      Finset.sum_image (fun x _ y _ h => hinj h)
    rw [← himg]
    refine hinv _ ?_
    intro n hn
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
    exact ha3 i
  have hnn : ∀ i, (0 : ℚ) ≤ 1 / ((a i : ℚ) * ((a i : ℚ) - 1)) := by
    intro i
    have h3 : (3 : ℚ) ≤ (a i : ℚ) := by exact_mod_cast ha3 i
    apply div_nonneg zero_le_one
    nlinarith
  -- `∏ (1 + xᵢ) ≤ 1 + 2 ∑ xᵢ` whenever the partial sums stay below `1/2`
  have hprod : ∀ s : Finset ι, (∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 1 / 2 →
      ∏ i ∈ s, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)))
        ≤ 1 + 2 * ∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert j s hj ih =>
      intro hle
      rw [Finset.sum_insert hj] at hle
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      have hx := hnn j
      have hS : (∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 1 / 2 := by linarith
      have hSnn : (0 : ℚ) ≤ ∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) :=
        Finset.sum_nonneg fun i _ => hnn i
      have hih := ih hS
      nlinarith [hih, hx, hS, hSnn]
  have hfin := hprod Finset.univ hsum
  show ∏ i, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 2
  linarith
