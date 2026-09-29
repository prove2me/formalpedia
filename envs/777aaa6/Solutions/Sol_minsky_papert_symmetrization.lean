-- Prove2me | solution 1 for minsky_papert_symmetrization
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-09T02:12:24.058184+00:00
-- url     : https://prove2.me/submissions/cce3dc2c-4b15-4d89-9ac8-abf4631bdb15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_minsky_papert_symmetrization
import Theorems.Thm_weight_count_with_subset
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Proof — `minsky_papert_symmetrization`

Construct the univariate witness via:
  `Q := ∑ m ∈ p.support, C (coeff m p / b.descFactorial m.support.card)
              * descPochhammer ℝ m.support.card`.
-/

open MvPolynomial Polynomial

namespace MinskyPapert

variable {b : ℕ}

/-- The univariate polynomial witness. -/
noncomputable def witness (p : MvPolynomial (Fin b) ℝ) : Polynomial ℝ :=
  ∑ m ∈ p.support,
    Polynomial.C (MvPolynomial.coeff m p / (b.descFactorial m.support.card : ℝ)) *
      descPochhammer ℝ m.support.card

/-- Each summand of `witness p` has degree at most `m.support.card`. -/
lemma summand_natDegree_le (m : Fin b →₀ ℕ) (c : ℝ) :
    (Polynomial.C c * descPochhammer ℝ m.support.card).natDegree
      ≤ m.support.card := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree (R := ℝ)]

/-- Support cardinality is at most the multi-index degree. -/
lemma support_card_le_totalDegree {p : MvPolynomial (Fin b) ℝ} {m : Fin b →₀ ℕ}
    (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intros i hi
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- Q.natDegree ≤ p.totalDegree. -/
lemma witness_natDegree_le (p : MvPolynomial (Fin b) ℝ) :
    (witness p).natDegree ≤ p.totalDegree := by
  classical
  unfold witness
  apply Polynomial.natDegree_sum_le_of_forall_le
  intros m hm
  exact (summand_natDegree_le m _).trans (support_card_le_totalDegree hm)

/-! ### Boolean-cube monomial evaluation -/

/-- For `i ∈ m.support`, `(boolToReal y i)^(m i) = boolToReal y i`. -/
lemma boolPow_eq_self_on_support {m : Fin b →₀ ℕ} {i : Fin b}
    (hi : i ∈ m.support) (y : Fin b → Bool) :
    (if y i then (1 : ℝ) else 0) ^ (m i) = (if y i then (1 : ℝ) else 0) := by
  have h1 : 1 ≤ m i :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  cases h : y i
  · simp [zero_pow (Nat.one_le_iff_ne_zero.mp h1)]
  · simp

/-- The product `∏_{i ∈ S} boolToReal y i` is `1` iff `S ⊆ trueSet y`, else `0`. -/
lemma prod_boolReal_indicator (S : Finset (Fin b)) (y : Fin b → Bool) :
    (∏ i ∈ S, (if y i then (1 : ℝ) else 0))
      = if S ⊆ (Finset.univ : Finset (Fin b)).filter (fun j => y j = true)
        then (1 : ℝ) else 0 := by
  classical
  by_cases hsub :
      S ⊆ (Finset.univ : Finset (Fin b)).filter (fun j => y j = true)
  · rw [if_pos hsub]
    apply Finset.prod_eq_one
    intros i hi
    have h_in : i ∈ (Finset.univ : Finset (Fin b)).filter (fun j => y j = true) := hsub hi
    rw [Finset.mem_filter] at h_in
    rw [h_in.2]
    simp
  · rw [if_neg hsub]
    obtain ⟨i, hi, hi_notin⟩ := Finset.not_subset.mp hsub
    apply Finset.prod_eq_zero hi
    have hyi : y i ≠ true := by
      intro hyi
      apply hi_notin
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hyi⟩
    cases h : y i
    · simp
    · exact absurd h hyi

/-- For monomial `m c`, on Boolean inputs, `eval y (monomial m c) = c · indicator`. -/
lemma eval_monomial_indicator (m : Fin b →₀ ℕ) (c : ℝ) (y : Fin b → Bool) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
        (MvPolynomial.monomial m c)
      = c * (if m.support ⊆ (Finset.univ : Finset (Fin b)).filter (fun j => y j = true)
              then (1 : ℝ) else 0) := by
  classical
  rw [MvPolynomial.eval_monomial, Finsupp.prod]
  congr 1
  rw [show (∏ i ∈ m.support, (if y i then (1 : ℝ) else 0) ^ m i)
        = ∏ i ∈ m.support, (if y i then (1 : ℝ) else 0) from ?_]
  · exact prod_boolReal_indicator m.support y
  · apply Finset.prod_congr rfl
    intros i hi
    exact boolPow_eq_self_on_support hi y

/-! ### Combinatorial identity in ℕ -/

/-- `t.descFactorial k · b.choose t = b.descFactorial k · count`, where
    `count = (b - k).choose (t - k)` for `k ≤ t`, else `0`. -/
lemma descFactorial_choose_count_identity (k t b : ℕ) :
    t.descFactorial k * b.choose t
      = b.descFactorial k *
          (if k ≤ t then (b - k).choose (t - k) else 0) := by
  by_cases hk : k ≤ t
  · rw [if_pos hk]
    rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose]
    rw [show (k.factorial * t.choose k) * b.choose t
            = k.factorial * (t.choose k * b.choose t) by ring]
    rw [show (k.factorial * b.choose k) * (b - k).choose (t - k)
            = k.factorial * (b.choose k * (b - k).choose (t - k)) by ring]
    congr 1
    have h_cm := Nat.choose_mul (n := b) (k := t) (s := k) hk
    linarith [h_cm]
  · rw [if_neg hk, Nat.mul_zero]
    have hk' : t < k := Nat.lt_of_not_le hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk', Nat.zero_mul]

/-- Per-monomial contribution to the LHS. -/
lemma summand_eval_eq_count (m : Fin b →₀ ℕ) (c : ℝ) (t : ℕ) :
    (Polynomial.C (c / (b.descFactorial m.support.card : ℝ))
        * descPochhammer ℝ m.support.card).eval (t : ℝ)
      * ((b.choose t : ℕ) : ℝ)
      = c * ((if m.support.card ≤ t then
                (b - m.support.card).choose (t - m.support.card)
              else 0 : ℕ) : ℝ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C,
      descPochhammer_eval_eq_descFactorial (R := ℝ) t m.support.card]
  have hk_le_b : m.support.card ≤ b := by
    have : m.support.card ≤ Fintype.card (Fin b) := Finset.card_le_univ _
    simpa [Fintype.card_fin] using this
  have hb_desc_pos : 0 < b.descFactorial m.support.card := by
    have h_general : ∀ k, k ≤ b → 0 < b.descFactorial k := by
      intros k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.descFactorial_succ]
        exact Nat.mul_pos (by omega) (ih (by omega))
    exact h_general _ hk_le_b
  have hb_desc_ne : (b.descFactorial m.support.card : ℝ) ≠ 0 := by
    have hpos : (b.descFactorial m.support.card : ℝ) > 0 := by exact_mod_cast hb_desc_pos
    linarith
  -- Apply the ℕ identity, casting through ℝ
  have h_id : t.descFactorial m.support.card * b.choose t
              = b.descFactorial m.support.card *
                (if m.support.card ≤ t then
                  (b - m.support.card).choose (t - m.support.card)
                else 0) :=
    descFactorial_choose_count_identity m.support.card t b
  have h_id_cast :
      (t.descFactorial m.support.card : ℝ) * ((b.choose t : ℕ) : ℝ)
      = (b.descFactorial m.support.card : ℝ)
        * (((if m.support.card ≤ t then
              (b - m.support.card).choose (t - m.support.card)
            else 0 : ℕ) : ℝ)) := by exact_mod_cast h_id
  field_simp
  linear_combination c * h_id_cast

end MinskyPapert

open MinskyPapert

theorem solution
    {b : ℕ} (p : MvPolynomial (Fin b) ℝ) :
    ∃ Q : Polynomial ℝ,
      Q.natDegree ≤ p.totalDegree ∧
      ∀ t : ℕ, t ≤ b →
        Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) =
          ∑ y ∈ (Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t),
            MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p := by
  classical
  refine ⟨witness p, witness_natDegree_le p, ?_⟩
  intros t _ht
  -- LHS: distribute Q.eval over the sum, apply summand_eval_eq_count
  unfold witness
  rw [Polynomial.eval_finset_sum, Finset.sum_mul]
  have h_LHS : ∀ m ∈ p.support,
      (Polynomial.C (MvPolynomial.coeff m p / (b.descFactorial m.support.card : ℝ))
          * descPochhammer ℝ m.support.card).eval (t : ℝ)
        * ((b.choose t : ℕ) : ℝ)
      = MvPolynomial.coeff m p
        * ((if m.support.card ≤ t then
              (b - m.support.card).choose (t - m.support.card)
            else 0 : ℕ) : ℝ) := by
    intros m _
    exact summand_eval_eq_count m _ t
  rw [Finset.sum_congr rfl h_LHS]
  -- RHS: rewrite eval y p as a sum over m, then swap.
  have h_RHS_eval : ∀ y : Fin b → Bool,
      MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p
      = ∑ m ∈ p.support, MvPolynomial.coeff m p
            * (if m.support ⊆ (Finset.univ : Finset (Fin b)).filter
                                (fun j => y j = true)
                then (1 : ℝ) else 0) := by
    intros y
    conv_lhs => rw [p.as_sum, MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intros m _
    exact eval_monomial_indicator m _ y
  rw [Finset.sum_congr rfl (fun y _ => h_RHS_eval y)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros m hm
  rw [← Finset.mul_sum]
  congr 1
  -- Goal: (count : ℝ) = ∑_{|y|=t} indicator(m.support ⊆ trueSet y)
  rw [← weight_count_with_subset m.support t]
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const]
  simp
