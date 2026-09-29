-- Prove2me | solution 2 for minsky_papert_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T02:25:11.629222+00:00
-- url     : https://prove2.me/submissions/f44820fc-f529-4529-9e28-96c18165978a

import Theorems.Thm_minsky_papert_symmetrization
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset

open Polynomial Finset

namespace MPsym

/-! ### The binomial-coefficient polynomial `X ↦ C(X, k)` -/

noncomputable def cpoly (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k

lemma cpoly_natDegree_le (k : ℕ) : (cpoly k).natDegree ≤ k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, descPochhammer_natDegree, zero_add]

lemma cpoly_eval (n k : ℕ) : (cpoly k).eval (n : ℝ) = (n.choose k : ℝ) := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hdp : (descPochhammer ℝ k).eval (n : ℝ) = (n.descFactorial k : ℝ) := by
    exact_mod_cast descPochhammer_eval_eq_descFactorial ℝ n k
  rw [cpoly, Polynomial.eval_mul, Polynomial.eval_C, hdp, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-! ### Vandermonde-type binomial identity -/

lemma choose_mul_eq {b t k : ℕ} (hk : k ≤ t) (ht : t ≤ b) :
    t.choose k * b.choose t = b.choose k * (b - k).choose (t - k) := by
  have hkb : k ≤ b := hk.trans ht
  have htk : t - k ≤ b - k := Nat.sub_le_sub_right ht k
  have hbkt : b - k - (t - k) = b - t := by omega
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < k.factorial * (t - k).factorial * (b - t).factorial by positivity)
  have hL : t.choose k * b.choose t * (k.factorial * (t - k).factorial * (b - t).factorial)
      = (t.choose k * k.factorial * (t - k).factorial) * (b.choose t * (b - t).factorial) := by ring
  have hR : b.choose k * (b - k).choose (t - k) * (k.factorial * (t - k).factorial * (b - t).factorial)
      = (b.choose k * k.factorial) * ((b - k).choose (t - k) * (t - k).factorial * (b - t).factorial) := by ring
  rw [hL, hR, Nat.choose_mul_factorial_mul_factorial hk]
  rw [show (b - k).choose (t - k) * (t - k).factorial * (b - t).factorial
        = (b - k).choose (t - k) * (t - k).factorial * ((b - k) - (t - k)).factorial by rw [hbkt]]
  rw [Nat.choose_mul_factorial_mul_factorial htk]
  have h1 : b.choose t * t.factorial * (b - t).factorial = b.factorial :=
    Nat.choose_mul_factorial_mul_factorial ht
  have h2 : b.choose k * k.factorial * (b - k).factorial = b.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkb
  calc t.factorial * (b.choose t * (b - t).factorial)
      = b.choose t * t.factorial * (b - t).factorial := by ring
    _ = b.factorial := h1
    _ = b.choose k * k.factorial * (b - k).factorial := h2.symm

/-! ### Counting -/

lemma count_weight_supset {b : ℕ} (S : Finset (Fin b)) {t : ℕ} (hSt : S.card ≤ t) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
        ∀ i ∈ S, y i = true)).card =
    (b - S.card).choose (t - S.card) := by
  have hbij :
      ((univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
          ∀ i ∈ S, y i = true)).card
      = ((univ \ S).powersetCard (t - S.card)).card := by
    refine Finset.card_bij'
      (fun y _ => (univ.filter (fun i => y i = true)) \ S)
      (fun T _ => (fun i => decide (i ∈ T ∨ i ∈ S)))
      ?_ ?_ ?_ ?_
    · rintro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      obtain ⟨hwt, hall⟩ := hy
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [mem_sdiff, mem_filter, mem_univ, true_and] at hi ⊢
        exact hi.2
      · have hSsub : S ⊆ univ.filter (fun i => y i = true) := by
          intro i hi
          simp only [mem_filter, mem_univ, true_and]
          exact hall i hi
        rw [Finset.card_sdiff, hwt, Finset.inter_eq_left.mpr hSsub]
    · rintro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      simp only [mem_filter, mem_univ, true_and]
      have hdisj : Disjoint T S := by
        rw [Finset.disjoint_left]
        intro i hiT hiS
        have := hTsub hiT
        simp only [mem_sdiff] at this
        exact this.2 hiS
      refine ⟨?_, ?_⟩
      · have hfeq : (univ.filter (fun i => decide (i ∈ T ∨ i ∈ S) = true)) = T ∪ S := by
          ext i
          simp [Finset.mem_union]
        rw [hfeq, Finset.card_union_of_disjoint hdisj, hTcard]
        omega
      · intro i hi
        simp [hi]
    · rintro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      funext i
      by_cases hiS : i ∈ S
      · simp only [decide_eq_true_eq]
        rw [hy.2 i hiS]
        simp [hiS]
      · simp only [decide_eq_true_eq, mem_sdiff, mem_filter, mem_univ, true_and, hiS,
          or_false, and_true]
        cases h : y i <;> simp [h]
    · rintro T hT
      rw [Finset.mem_powersetCard] at hT
      ext i
      simp only [mem_sdiff, mem_filter, mem_univ, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨hor, hiS⟩
        rcases hor with h | h
        · exact h
        · exact absurd h hiS
      · intro hiT
        have := hT.1 hiT
        simp only [mem_sdiff] at this
        exact ⟨Or.inl hiT, this.2⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

lemma count_weight_supset_zero {b : ℕ} (S : Finset (Fin b)) {t : ℕ} (hSt : t < S.card) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
        ∀ i ∈ S, y i = true)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _
  intro hyp
  obtain ⟨hwt, hall⟩ := hyp
  have hSsub : S ⊆ univ.filter (fun i => y i = true) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact hall i hi
  have := Finset.card_le_card hSsub
  omega

/-! ### The monomial piece -/

noncomputable def Qmono {b : ℕ} (α : Fin b →₀ ℕ) : Polynomial ℝ :=
  Polynomial.C ((b.choose α.support.card : ℝ)⁻¹) * cpoly α.support.card

lemma Qmono_natDegree_le {b : ℕ} (α : Fin b →₀ ℕ) : (Qmono α).natDegree ≤ α.support.card := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact cpoly_natDegree_le _

lemma eval_monomial_at_bool {b : ℕ} (α : Fin b →₀ ℕ) (y : Fin b → Bool) :
    MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ))
      = if ∀ i ∈ α.support, y i = true then (1 : ℝ) else 0 := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  calc ∏ i ∈ α.support, (if y i = true then (1:ℝ) else 0) ^ α i
      = ∏ i ∈ α.support, (if y i = true then (1:ℝ) else 0) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        have hαi : α i ≠ 0 := Finsupp.mem_support_iff.mp hi
        cases h : y i
        · simp [h, zero_pow hαi]
        · simp [h]
    _ = if ∀ i ∈ α.support, y i = true then (1:ℝ) else 0 := by
        split_ifs with hall
        · exact Finset.prod_eq_one (fun i hi => by simp [hall i hi])
        · push_neg at hall
          obtain ⟨i, hiS, hyi⟩ := hall
          exact Finset.prod_eq_zero hiS (if_neg hyi)

lemma Qmono_eval_eq {b : ℕ} (α : Fin b →₀ ℕ) {t : ℕ} (ht : t ≤ b) :
    (Qmono α).eval (t : ℝ) * (b.choose t : ℝ)
      = ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
            (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ)) := by
  set k := α.support.card with hkdef
  have hkb : k ≤ b := by
    calc k ≤ (univ : Finset (Fin b)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = b := by rw [Finset.card_univ, Fintype.card_fin]
  have hRHS : (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
      MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ)))
      = (((univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
            ∀ i ∈ α.support, y i = true)).card : ℝ) := by
    simp only [eval_monomial_at_bool]
    rw [Finset.sum_boole, Finset.filter_filter]
  rw [hRHS, Qmono, Polynomial.eval_mul, Polynomial.eval_C, cpoly_eval]
  by_cases hkt : k ≤ t
  · rw [count_weight_supset α.support hkt]
    have hbcn : (b.choose k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hkb).ne'
    rw [show (↑(b.choose k) : ℝ)⁻¹ * (↑(t.choose k)) * (↑(b.choose t))
          = (↑(t.choose k) * ↑(b.choose t)) / (↑(b.choose k)) from by ring]
    rw [div_eq_iff hbcn]
    exact_mod_cast (choose_mul_eq hkt ht).trans (Nat.mul_comm _ _)
  · push_neg at hkt
    rw [count_weight_supset_zero α.support hkt]
    rw [Nat.choose_eq_zero_of_lt hkt]
    simp

lemma card_support_le_sum {b : ℕ} (α : Fin b →₀ ℕ) :
    α.support.card ≤ α.sum (fun _ e => e) := by
  rw [Finsupp.sum]
  calc α.support.card = ∑ _i ∈ α.support, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ α.support, α i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

end MPsym

open MPsym

theorem solution : minsky_papert_symmetrization := by
  intro b p
  refine ⟨∑ α ∈ p.support, Polynomial.C (MvPolynomial.coeff α p) * Qmono α, ?_, ?_⟩
  · -- degree bound
    refine Polynomial.natDegree_le_iff_degree_le.mpr ?_
    refine (Polynomial.degree_sum_le _ _).trans ?_
    refine Finset.sup_le ?_
    intro α hα
    refine Polynomial.degree_le_natDegree.trans ?_
    refine Nat.cast_le.mpr ?_
    calc (Polynomial.C (MvPolynomial.coeff α p) * Qmono α).natDegree
        ≤ 0 + (Qmono α).natDegree := by
          refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_C]
      _ ≤ α.support.card := by rw [zero_add]; exact Qmono_natDegree_le α
      _ ≤ α.sum (fun _ e => e) := card_support_le_sum α
      _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hα
  · intro t ht
    rw [Polynomial.eval_finset_sum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, Qmono_eval_eq _ ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro y _
    conv_rhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    ring
