-- Prove2me | solution 1 for MarkovMixing.time_reversal
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:24:44.242796+00:00
-- url     : https://prove2.me/submissions/d102587a-39f6-4e98-b182-b50fcc69a80d

import Definitions.Def_mm_path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) :
    IsStochastic (timeReversal P π) ∧ IsStationary (timeReversal P π) π ∧
    ∀ (t : ℕ) (ω : Fin (t + 1) → V),
      π (ω 0) * pathWeight P ω =
        π (ω (Fin.last t)) * pathWeight (timeReversal P π) (fun i => ω i.rev) := by
  classical
  -- powers have nonnegative entries
  have hpow_nonneg : ∀ (s : ℕ) (a b : V), 0 ≤ (P ^ s) a b := by
    intro s
    induction s with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  -- π is stationary for every power
  have hstat_pow : ∀ s : ℕ, π ᵥ* (P ^ s) = π := by
    intro s
    induction s with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
  -- π is strictly positive
  have hpos : ∀ x : V, 0 < π x := by
    intro x
    obtain ⟨z, hz⟩ : ∃ z : V, 0 < π z := by
      by_contra hcon
      push_neg at hcon
      have hzero : ∀ z : V, π z = 0 := fun z => le_antisymm (hcon z) (hπ.1.1 z)
      have := hπ.1.2
      simp [hzero] at this
    obtain ⟨s, hs⟩ := hirr z x
    have hval : π x = ∑ w, π w * (P ^ s) w x := (congrFun (hstat_pow s) x).symm
    have hterm : π z * (P ^ s) z x ≤ ∑ w, π w * (P ^ s) w x :=
      Finset.single_le_sum (f := fun w => π w * (P ^ s) w x)
        (fun w _ => mul_nonneg (hπ.1.1 w) (hpow_nonneg s w x)) (Finset.mem_univ z)
    have : 0 < π z * (P ^ s) z x := mul_pos hz hs
    rw [hval]; linarith
  -- the reversal is stochastic
  have hrev_stoch : IsStochastic (timeReversal P π) := by
    constructor
    · intro x y
      exact div_nonneg (mul_nonneg (hπ.1.1 y) (hP.1 y x)) (hpos x).le
    · intro x
      have hcol : ∑ y, π y * P y x = π x := congrFun hπ.2 x
      have hterm : ∀ y : V, timeReversal P π x y = (π y * P y x) * (π x)⁻¹ := by
        intro y; show π y * P y x / π x = _; rw [div_eq_mul_inv]
      have : ∑ y, timeReversal P π x y = (∑ y, π y * P y x) / π x := by
        rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_mul, div_eq_mul_inv]
      rw [this, hcol, div_self (hpos x).ne']
  -- π is stationary for the reversal
  have hrev_stat : IsStationary (timeReversal P π) π := by
    refine ⟨hπ.1, ?_⟩
    funext y
    have h : (π ᵥ* timeReversal P π) y = ∑ x, π x * (π y * P y x / π x) := rfl
    rw [h]
    have hterm : ∀ x : V, π x * (π y * P y x / π x) = π y * P y x := by
      intro x
      have hx : π x ≠ 0 := (hpos x).ne'
      field_simp
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum, hP.2 y, mul_one]
  refine ⟨hrev_stoch, hrev_stat, ?_⟩
  intro t ω
  -- rewrite the reversed path weight as a product over the original index set
  have hrw : pathWeight (timeReversal P π) (fun i => ω i.rev)
      = ∏ j : Fin t, (π (ω j.castSucc) * P (ω j.castSucc) (ω j.succ) / π (ω j.succ)) := by
    have hstep : pathWeight (timeReversal P π) (fun i => ω i.rev)
        = ∏ i : Fin t, (π (ω (i.rev).castSucc) * P (ω (i.rev).castSucc) (ω (i.rev).succ)
            / π (ω (i.rev).succ)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Fin.rev_castSucc, Fin.rev_succ]
      rfl
    rw [hstep]
    exact Equiv.prod_comp Fin.revPerm
      (fun j : Fin t => π (ω j.castSucc) * P (ω j.castSucc) (ω j.succ) / π (ω j.succ))
  rw [hrw]
  -- telescoping identity for the π-factors
  have hA : ∏ i : Fin (t + 1), π (ω i)
      = (∏ j : Fin t, π (ω j.castSucc)) * π (ω (Fin.last t)) :=
    Fin.prod_univ_castSucc (fun i => π (ω i))
  have hB : ∏ i : Fin (t + 1), π (ω i)
      = π (ω 0) * ∏ j : Fin t, π (ω j.succ) :=
    Fin.prod_univ_succ (fun i => π (ω i))
  have hBne : (∏ j : Fin t, π (ω j.succ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => (hpos _).ne'
  have hsplit : ∏ j : Fin t, (π (ω j.castSucc) * P (ω j.castSucc) (ω j.succ) / π (ω j.succ))
      = ((∏ j : Fin t, π (ω j.castSucc)) * ∏ j : Fin t, P (ω j.castSucc) (ω j.succ))
        / ∏ j : Fin t, π (ω j.succ) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [hsplit]
  have hkey : (∏ j : Fin t, π (ω j.castSucc)) * π (ω (Fin.last t))
      = π (ω 0) * ∏ j : Fin t, π (ω j.succ) := by rw [← hA, hB]
  have hpw : pathWeight P ω = ∏ j : Fin t, P (ω j.castSucc) (ω j.succ) := rfl
  rw [hpw]
  have hreassoc : π (ω (Fin.last t))
        * (((∏ j : Fin t, π (ω j.castSucc)) * ∏ j : Fin t, P (ω j.castSucc) (ω j.succ))
            / ∏ j : Fin t, π (ω j.succ))
      = (((∏ j : Fin t, π (ω j.castSucc)) * π (ω (Fin.last t)))
            * ∏ j : Fin t, P (ω j.castSucc) (ω j.succ))
          / ∏ j : Fin t, π (ω j.succ) := by ring
  rw [hreassoc, hkey]
  field_simp
