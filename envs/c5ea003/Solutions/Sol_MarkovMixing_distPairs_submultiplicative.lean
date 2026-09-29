-- Prove2me | solution 1 for MarkovMixing.distPairs_submultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:05:14.621446+00:00
-- url     : https://prove2.me/submissions/09f6c3d8-a575-41d0-9461-007d570e3951

import Theorems.Thm_MarkovMixing_tv_coupling
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P) (s t : ℕ) :
    distPairs P (s + t) ≤ distPairs P s * distPairs P t := by
  classical
  -- rows of every power are probability distributions
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hpow_row : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  have hrowdist : ∀ (n : ℕ) (a : V), IsDist (rowDist P n a) :=
    fun n a => ⟨fun b => hpow_nonneg n a b, hpow_row n a⟩
  -- generic supremum facts
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have htv_ge : ∀ (μ ν : V → ℝ) (A : Finset V),
      |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν :=
    fun μ ν A => le_ciSup (hbdd μ ν) A
  have htv_nonneg : ∀ μ ν : V → ℝ, 0 ≤ tvDist μ ν := by
    intro μ ν
    have h := htv_ge μ ν ∅
    simpa using h
  have hbdd_dbar : ∀ n : ℕ,
      BddAbove (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)) :=
    fun n => Set.Finite.bddAbove
      (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)).toFinite
  have hdbar_ge : ∀ (n : ℕ) (x y : V),
      tvDist (rowDist P n x) (rowDist P n y) ≤ distPairs P n :=
    fun n x y => le_ciSup (hbdd_dbar n) (x, y)
  have hdbar_nonneg : ∀ n : ℕ, 0 ≤ distPairs P n := fun n =>
    le_trans (htv_nonneg _ _) (hdbar_ge n (Classical.arbitrary V) (Classical.arbitrary V))
  refine ciSup_le fun p => ?_
  obtain ⟨x, y⟩ := p
  -- an optimal coupling of the two `s`-step rows
  obtain ⟨q, hq, hqval⟩ :=
    (MarkovMixing.tv_coupling (rowDist P s x) (rowDist P s y)
      (hrowdist s x) (hrowdist s y)).2
  refine ciSup_le fun A => ?_
  -- rewrite the (s+t)-step difference as an average over the coupling
  have hmass : ∀ (a : V), ∑ z ∈ A, (rowDist P (s + t) a) z
      = ∑ w, (P ^ s) a w * ∑ z ∈ A, (rowDist P t w) z := by
    intro a
    have e : ∀ z : V, (rowDist P (s + t) a) z = ∑ w, (P ^ s) a w * (P ^ t) w z := by
      intro z
      show (P ^ (s + t)) a z = _
      rw [pow_add]; rfl
    rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum]; rfl
  have hcouple : ∑ z ∈ A, (rowDist P (s + t) x) z - ∑ z ∈ A, (rowDist P (s + t) y) z
      = ∑ r : V × V, q r
          * (∑ z ∈ A, (rowDist P t r.1) z - ∑ z ∈ A, (rowDist P t r.2) z) := by
    have h1 : ∑ r : V × V, q r * ∑ z ∈ A, (rowDist P t r.1) z
        = ∑ z ∈ A, (rowDist P (s + t) x) z := by
      rw [Fintype.sum_prod_type, hmass x]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp only
      rw [← Finset.sum_mul, hq.2.1 w]
      rfl
    have h2 : ∑ r : V × V, q r * ∑ z ∈ A, (rowDist P t r.2) z
        = ∑ z ∈ A, (rowDist P (s + t) y) z := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, hmass y]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp only
      rw [← Finset.sum_mul, hq.2.2 w]
      rfl
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hcouple]
  -- bound each term of the average
  have hstep : ∀ r : V × V,
      |q r * (∑ z ∈ A, (rowDist P t r.1) z - ∑ z ∈ A, (rowDist P t r.2) z)|
      ≤ (if r.1 ≠ r.2 then q r else 0) * distPairs P t := by
    intro r
    by_cases hr : r.1 = r.2
    · have h0 : ∑ z ∈ A, (rowDist P t r.1) z - ∑ z ∈ A, (rowDist P t r.2) z = 0 := by
        rw [hr]; ring
      rw [h0, mul_zero, abs_zero, if_neg (not_not.mpr hr), zero_mul]
    · rw [if_pos hr, abs_mul, abs_of_nonneg (hq.1.1 r)]
      exact mul_le_mul_of_nonneg_left
        (le_trans (htv_ge _ _ A) (hdbar_ge t r.1 r.2)) (hq.1.1 r)
  calc |∑ r : V × V, q r
          * (∑ z ∈ A, (rowDist P t r.1) z - ∑ z ∈ A, (rowDist P t r.2) z)|
      ≤ ∑ r : V × V, |q r
          * (∑ z ∈ A, (rowDist P t r.1) z - ∑ z ∈ A, (rowDist P t r.2) z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : V × V, (if r.1 ≠ r.2 then q r else 0) * distPairs P t :=
        Finset.sum_le_sum fun r _ => hstep r
    _ = (∑ r ∈ Finset.univ.filter (fun r : V × V => r.1 ≠ r.2), q r) * distPairs P t := by
        rw [← Finset.sum_mul, ← Finset.sum_filter]
    _ = tvDist (rowDist P s x) (rowDist P s y) * distPairs P t := by rw [← hqval]
    _ ≤ distPairs P s * distPairs P t :=
        mul_le_mul_of_nonneg_right (hdbar_ge s x y) (hdbar_nonneg t)
