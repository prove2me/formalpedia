-- Prove2me | solution 1 for MarkovMixing.cycle_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:27:48.09681+00:00
-- url     : https://prove2.me/submissions/bd045e93-18fa-45db-b487-094145c31a94

import Definitions.Def_mm_spectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

open scoped BigOperators
open scoped Matrix
open MarkovMixing

/-- The phase attached to a natural number `m`: `cyc n j m = cos (2π j m / n)`.
This is the candidate eigenfunction, read along canonical representatives of
`ZMod n`. -/
private noncomputable def cyc (n : ℕ) (j : ℕ) (m : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * (j * m : ℕ) / n)

private lemma cyc_add_mul (n j m q : ℕ) (hn : n ≠ 0) :
    cyc n j (m + n * q) = cyc n j m := by
  unfold cyc
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (2 * Real.pi * ((j * (m + n * q) : ℕ) : ℝ) / n)
      = 2 * Real.pi * ((j * m : ℕ) : ℝ) / n + (j * q : ℕ) * (2 * Real.pi) := by
    push_cast
    field_simp
  rw [this, Real.cos_add_nat_mul_two_pi]

/-- `cyc` only depends on `m` modulo `n`, so it descends to `ZMod n`. -/
private lemma cyc_val (n : ℕ) [NeZero n] (j m : ℕ) :
    cyc n j ((m : ZMod n).val) = cyc n j m := by
  have hn : n ≠ 0 := NeZero.ne n
  have hval : (m : ZMod n).val = m % n := ZMod.val_natCast n m
  rw [hval]
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [cyc_add_mul n j (m % n) (m / n) hn]

theorem solution (n : ℕ) [NeZero n] (hn : 3 ≤ n) (j : Fin n) :
    IsEigenvalue (cycleWalk n) (Real.cos (2 * Real.pi * j / n)) := by
  classical
  have hn0 : n ≠ 0 := NeZero.ne n
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  set θ : ℝ := 2 * Real.pi * (j.val : ℝ) / n with hθ
  have hcast : ∀ x : ZMod n, ((x.val : ℕ) : ZMod n) = x := ZMod.natCast_rightInverse
  -- `cyc` in closed form
  have hcyc : ∀ m : ℕ, cyc n j.val m = Real.cos (θ * m) := by
    intro m
    unfold cyc
    congr 1
    rw [hθ]
    push_cast
    field_simp
  -- the two neighbours of `x` are distinct, because `n ≥ 3`
  have hne : ∀ x : ZMod n, x + 1 ≠ x - 1 := by
    intro x hx
    have h1 : (1 : ZMod n) = -1 := by
      have h := hx
      have : x + 1 - x = x - 1 - x := by rw [h]
      simpa using this
    have h2 : ((2 : ℕ) : ZMod n) = 0 := by
      push_cast
      linear_combination h1
    have hdvd := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- values at the two neighbours
  have hsucc : ∀ x : ZMod n, cyc n j.val (x + 1).val = Real.cos (θ * x.val + θ) := by
    intro x
    have hx : x + 1 = ((x.val + 1 : ℕ) : ZMod n) := by
      push_cast [hcast x]
      ring
    rw [hx, cyc_val, hcyc]
    push_cast
    ring_nf
  have hpred : ∀ x : ZMod n, cyc n j.val (x - 1).val = Real.cos (θ * x.val - θ) := by
    intro x
    have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
      have h : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
        have hh : (n - 1) + 1 = n := by omega
        calc ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by push_cast; ring
          _ = ((n : ℕ) : ZMod n) := by rw [hh]
          _ = 0 := ZMod.natCast_self n
      linear_combination h
    have hx : x - 1 = ((x.val + (n - 1) : ℕ) : ZMod n) := by
      push_cast [hcast x, hn1]
      ring
    rw [hx, cyc_val, hcyc]
    have hcs : ((x.val + (n - 1) : ℕ) : ℝ) = (x.val : ℝ) + (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcs]
    have hexp : θ * ((x.val : ℝ) + (n : ℝ) - 1)
        = θ * x.val - θ + (j.val : ℕ) * (2 * Real.pi) := by
      rw [hθ]
      field_simp
      ring
    rw [hexp, Real.cos_add_nat_mul_two_pi]
  refine ⟨fun x => cyc n j.val x.val, ?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero (0 : ZMod n)
    simp only [Pi.zero_apply] at h0
    rw [show ((0 : ZMod n)).val = 0 from ZMod.val_zero, hcyc] at h0
    simp at h0
  · funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ y : ZMod n, cycleWalk n x y * cyc n j.val y.val
        = if y ∈ ({x + 1, x - 1} : Finset (ZMod n)) then (2⁻¹ : ℝ) * cyc n j.val y.val
          else 0 := by
      intro y
      by_cases h : y = x + 1 ∨ y = x - 1
      · rw [if_pos (by simpa [Finset.mem_insert, Finset.mem_singleton] using h)]
        rw [show cycleWalk n x y = 1 / 2 from by simp [cycleWalk, h]]
        ring
      · rw [if_neg (by simpa [Finset.mem_insert, Finset.mem_singleton] using h)]
        rw [show cycleWalk n x y = 0 from by simp [cycleWalk, h]]
        ring
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_pair (hne x), hsucc x, hpred x, hcyc]
    rw [Real.cos_add, Real.cos_sub]
    ring
