-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.temporal_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:13:07.589156+00:00
-- url     : https://prove2.me/submissions/4f1d615f-b108-46e7-a561-8748e69477b8

import Mathlib
import Definitions.Def_Probability_RefractorySpikeTrains
open Catalog.Probability.NeuralCoding.Temporal in
theorem solution (m : ℕ) : Real.logb 2 ((trains (5 * m)).card) ≤ 0.8 * (5 * m) := by
  -- the refractory recursion, as an inequality
  have hrec : ∀ n, (trains (n + 2)).card ≤ (trains (n + 1)).card + (trains n).card := by
    intro n
    simp only [trains]
    exact le_trans (Finset.card_union_le _ _)
      (add_le_add Finset.card_image_le Finset.card_image_le)
  -- monotonicity: prefixing `false` embeds `trains (n+1)` into `trains (n+2)`
  have hmono : ∀ n, (trains n).card ≤ (trains (n + 1)).card := by
    intro n
    match n with
    | 0 => simp [trains]
    | (k + 1) =>
      have hinj : Function.Injective (fun l : List Bool => false :: l) := by
        intro a b h
        simpa using h
      calc (trains (k + 1)).card
          = ((trains (k + 1)).image (fun l => false :: l)).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ (trains (k + 2)).card := by
            simp only [trains]
            exact Finset.card_le_card Finset.subset_union_left
  have hdouble : ∀ n, (trains (n + 1)).card ≤ 2 * (trains n).card := by
    intro n
    match n with
    | 0 => simp [trains]
    | (k + 1) =>
      show (trains (k + 2)).card ≤ 2 * (trains (k + 1)).card
      have h1 := hrec k
      have h2 := hmono k
      omega
  -- five steps multiply the count by at most 16
  have hstep : ∀ n, (trains (n + 5)).card ≤ 16 * (trains n).card := by
    intro n
    have a1 : (trains (n + 2)).card ≤ (trains (n + 1)).card + (trains n).card := hrec n
    have a2 : (trains (n + 3)).card ≤ (trains (n + 2)).card + (trains (n + 1)).card := hrec (n + 1)
    have a3 : (trains (n + 4)).card ≤ (trains (n + 3)).card + (trains (n + 2)).card := hrec (n + 2)
    have a4 : (trains (n + 5)).card ≤ (trains (n + 4)).card + (trains (n + 3)).card := hrec (n + 3)
    have d0 : (trains (n + 1)).card ≤ 2 * (trains n).card := hdouble n
    omega
  have hpow : ∀ k, (trains (5 * k)).card ≤ 16 ^ k := by
    intro k
    induction k with
    | zero => simp [trains]
    | succ j ih =>
      have h5 : 5 * (j + 1) = 5 * j + 5 := by ring
      rw [h5]
      calc (trains (5 * j + 5)).card ≤ 16 * (trains (5 * j)).card := hstep (5 * j)
        _ ≤ 16 * 16 ^ j := by omega
        _ = 16 ^ (j + 1) := by ring
  have hpos : 1 ≤ (trains (5 * m)).card := by
    have h : ∀ n, 1 ≤ (trains n).card := by
      intro n
      induction n with
      | zero => simp [trains]
      | succ j ih => exact le_trans ih (hmono j)
    exact h _
  -- pass to logarithms
  have hposR : (0 : ℝ) < ((trains (5 * m)).card : ℝ) := by
    have : (1 : ℝ) ≤ ((trains (5 * m)).card : ℝ) := by exact_mod_cast hpos
    linarith
  have hleR : ((trains (5 * m)).card : ℝ) ≤ (16 : ℝ) ^ m := by
    have h := hpow m
    have : ((trains (5 * m)).card : ℝ) ≤ ((16 ^ m : ℕ) : ℝ) := by exact_mod_cast h
    simpa using this
  have h16 : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
  calc Real.logb 2 ((trains (5 * m)).card)
      ≤ Real.logb 2 ((16 : ℝ) ^ m) :=
        (Real.logb_le_logb (by norm_num) hposR h16).mpr hleR
    _ = 4 * m := by
        rw [Real.logb_pow, show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one]
        · ring
        · norm_num
    _ = 0.8 * (5 * m) := by
        rw [show (0.8 : ℝ) = 4 / 5 by norm_num]
        ring
