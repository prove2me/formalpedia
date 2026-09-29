-- Prove2me | solution 1 for polyDegree_alternating_sum_witness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-06T20:44:25.022451+00:00
-- url     : https://prove2.me/submissions/93e209df-da50-4918-9a5a-3450fa3f5166

import Theorems.Thm_polyDegree_alternating_sum_witness
import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Definitions.Def_Mobius
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MvPolynomial BooleanInterpolation Mobius Finset

/-!
# Proof — `polyDegree_alternating_sum_witness`

Direct alt-sum proof. For `f : BoolFunc n` with `polyDegree f = d ≥ 1`,
exhibit an `S` of size `d` with non-zero `altSum f S`.

Strategy:
1. (`altSum_zero_above_totalDegree`) For any polynomial `p` representing
   `f` with `totalDegree p ≤ d` and any `S` with `|S| > d`,
   `altSum f S = 0`.
2. (Contradiction polynomial) If `altSum f S = 0` for all `|S| ≥ d`,
   build `q := ∑_{|S| < d} altSum f S · ∏_{i ∈ S} X_i` representing `f`
   at degree `≤ d − 1`, contradicting `polyDegree f = d`.
3. Combine: `|S| ≥ d` with `altSum ≠ 0` exists; `|S| > d` is excluded.
   So `|S| = d`.
-/

namespace PolyDegAltSum

variable {n : ℕ}

/-- Real cube vertex from a Bool one (as a function). -/
noncomputable def realFromBool (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if x i then (1 : ℝ) else 0

@[simp] lemma realFromBool_boolOfFinset (T : Finset (Fin n)) :
    realFromBool (boolOfFinset T) = realVertex T := by
  funext i
  simp only [realFromBool, boolOfFinset_apply, realVertex]
  by_cases h : i ∈ T <;> simp [h]

/-- For `s : Fin n →₀ ℕ` and a cube indicator `realVertex T`, the Finsupp.prod
    `∏_{i ∈ s.support} (realVertex T i)^(s i) = 1` if `s.support ⊆ T`, else `0`. -/
lemma finsupp_prod_realVertex (s : Fin n →₀ ℕ) (T : Finset (Fin n)) :
    (s.prod fun i e => realVertex T i ^ e) = if s.support ⊆ T then (1 : ℝ) else 0 := by
  classical
  rw [Finsupp.prod]
  by_cases h : s.support ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hi_pos : 0 < s i := by
      have : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
      omega
    have h_in : i ∈ T := h hi
    simp only [realVertex, if_pos h_in]
    exact one_pow _
  · rw [if_neg h]
    rw [Finset.subset_iff] at h
    push_neg at h
    obtain ⟨i, hi_supp, hi_notT⟩ := h
    have hi_pos : 0 < s i := by
      have : s i ≠ 0 := Finsupp.mem_support_iff.mp hi_supp
      omega
    apply Finset.prod_eq_zero hi_supp
    simp only [realVertex, if_neg hi_notT]
    exact zero_pow (Nat.pos_iff_ne_zero.mp hi_pos)

/-- For any polynomial `p`, `eval (realVertex T) p = ∑_{s ∈ supp p, supp s ⊆ T} p.coeff s`. -/
lemma eval_at_realVertex (p : MvPolynomial (Fin n) ℝ) (T : Finset (Fin n)) :
    eval (realVertex T) p =
      ∑ s ∈ p.support.filter (fun s => s.support ⊆ T), p.coeff s := by
  classical
  -- Express p as a sum of monomials.
  conv_lhs => rw [p.as_sum]
  rw [eval_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  rw [eval_monomial, finsupp_prod_realVertex]
  by_cases h : s.support ⊆ T
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- For any polynomial `p` representing `f` with `totalDegree p ≤ d` and any
    `S` with `|S| > d`, `altSum f S = 0`. -/
lemma altSum_zero_above_totalDegree
    (f : BoolFunc n) (p : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (h_td : p.totalDegree ≤ d)
    (h_eval : ∀ x : Fin n → Bool, eval (realFromBool x) p = realOf (f x))
    (S : Finset (Fin n)) (hS : d < S.card) :
    altSum f S = 0 := by
  classical
  -- realOf (f (boolOfFinset T)) = eval (realVertex T) p.
  have h_subst : ∀ T : Finset (Fin n),
      realOf (f (boolOfFinset T)) = eval (realVertex T) p := by
    intro T
    rw [← realFromBool_boolOfFinset]
    exact (h_eval (boolOfFinset T)).symm
  -- Rewrite altSum f S using the substitution.
  have h_rewrite : altSum f S =
      ∑ s ∈ p.support, p.coeff s *
        (∑ T ∈ S.powerset.filter (s.support ⊆ ·), signR (S.card - T.card)) := by
    unfold altSum
    -- Substitute realOf → eval.
    rw [Finset.sum_congr rfl (fun T _ => by rw [h_subst T])]
    -- Substitute eval → ∑ filter.
    rw [Finset.sum_congr rfl (fun T _ => by rw [eval_at_realVertex p T])]
    -- Pull signR into the inner sum (mul_sum).
    rw [Finset.sum_congr rfl (fun T _ => Finset.mul_sum _ _ _)]
    -- Convert inner filter sum → if-then-else.
    rw [Finset.sum_congr rfl (fun T _ => by rw [Finset.sum_filter])]
    -- LHS now: ∑ T ∈ S.powerset, ∑ s ∈ p.support, if s.support ⊆ T then signR * coeff else 0.
    -- Swap sums.
    rw [Finset.sum_comm]
    -- Goal: ∑ s ∈ p.support, ∑ T ∈ S.powerset, if-then-else = ∑ s, coeff * ∑ T ∈ filter, signR.
    apply Finset.sum_congr rfl
    intro s _
    -- Convert RHS filter → if-then-else, then mul_sum.
    rw [Finset.sum_filter]
    rw [Finset.mul_sum]
    -- Goal: ∑ T, (if then signR*coeff else 0) = ∑ T, coeff * (if then signR else 0).
    apply Finset.sum_congr rfl
    intro T _
    by_cases h : s.support ⊆ T
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [h_rewrite]
  -- Each summand is 0: |supp(s)| ≤ s.sum ≤ totalDegree ≤ d < |S|.
  apply Finset.sum_eq_zero
  intro s hs_supp
  -- |supp(s)| ≤ d.
  have h_sum_le : (s.sum fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hs_supp
  have h_card_le_sum : s.support.card ≤ (s.sum fun _ e => e) := by
    rw [Finsupp.sum, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro i hi
    have : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
    omega
  have h_card_supp : s.support.card ≤ d := by omega
  -- Inner sum analysis.
  by_cases h_sub : s.support ⊆ S
  · -- supp(s) ⊆ S, but supp(s) ≠ S (since |supp| ≤ d < |S|).
    have h_ne : s.support ≠ S := by
      intro heq; rw [heq] at h_card_supp; omega
    rw [inner_sum_collapse_compl s.support h_sub, if_neg h_ne, mul_zero]
  · -- supp(s) ⊄ S: filter is empty.
    have h_empty : (S.powerset.filter (s.support ⊆ ·)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      exact h_sub (hT.2.trans hT.1)
    rw [h_empty, Finset.sum_empty, mul_zero]

/-- The contradiction polynomial: when `altSum f S = 0` for all `|S| ≥ d`,
    `truncFromAlt f d` represents `f`. -/
noncomputable def truncFromAlt (f : BoolFunc n) (d : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card < d),
    altSum f S • ∏ i ∈ S, (X i : MvPolynomial (Fin n) ℝ)

lemma truncFromAlt_totalDegree_lt (f : BoolFunc n) (d : ℕ) (hd : 1 ≤ d) :
    (truncFromAlt f d).totalDegree ≤ d - 1 := by
  classical
  unfold truncFromAlt
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  refine (totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc (∑ i ∈ S, (X i : MvPolynomial (Fin n) ℝ).totalDegree)
      ≤ ∑ _i ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro i _
        rw [MvPolynomial.totalDegree_X]
    _ = S.card := by simp
    _ ≤ d - 1 := by omega

lemma truncFromAlt_eval (f : BoolFunc n) (d : ℕ) (y : Fin n → Bool) :
    eval (realFromBool y) (truncFromAlt f d) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card < d),
        (if S ⊆ trueSet y then altSum f S else 0) := by
  classical
  show eval (realFromBool y)
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card < d),
        altSum f S • ∏ i ∈ S, (X i : MvPolynomial (Fin n) ℝ)) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro S _
  -- realFromBool y = realVertex (trueSet y).
  have h_eq : realFromBool y = realVertex (trueSet y) := by
    funext i
    simp [realFromBool, realVertex, mem_trueSet]
  rw [h_eq, smul_eval]
  -- eval at squarefree monomial.
  rw [show eval (realVertex (trueSet y)) (∏ i ∈ S, (X i : MvPolynomial (Fin n) ℝ))
        = if S ⊆ trueSet y then (1 : ℝ) else 0 from by
    rw [eval_prod]
    by_cases h : S ⊆ trueSet y
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i hi
      rw [eval_X]; simp only [realVertex, if_pos (h hi)]
    · rw [if_neg h]
      rw [Finset.subset_iff] at h
      push_neg at h
      obtain ⟨i, hi_S, hi_notT⟩ := h
      apply Finset.prod_eq_zero hi_S
      rw [eval_X]; simp only [realVertex, if_neg hi_notT]]
  by_cases h : S ⊆ trueSet y
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

lemma truncFromAlt_represents
    (f : BoolFunc n) (d : ℕ) (hd : 1 ≤ d)
    (h_alt_zero : ∀ S : Finset (Fin n), d ≤ S.card → altSum f S = 0)
    (y : Fin n → Bool) :
    eval (realFromBool y) (truncFromAlt f d) = realOf (f y) := by
  classical
  rw [truncFromAlt_eval, mobius_inversion f y]
  -- Convert LHS sum to ∑ S ⊆ trueSet y with |S| < d.
  rw [show (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card < d),
            (if S ⊆ trueSet y then altSum f S else 0))
        = ∑ S ∈ (trueSet y).powerset.filter (fun S => S.card < d), altSum f S from by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨_, hcard⟩, hsub⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨Finset.subset_univ _, hcard⟩, hsub⟩]
  -- Now goal: ∑ S ⊆ trueSet y, |S| < d, altSum f S = ∑ S ⊆ trueSet y, altSum f S.
  -- Difference: ∑ S ⊆ trueSet y, d ≤ |S|, altSum f S = 0 by h_alt_zero.
  rw [show (∑ S ∈ (trueSet y).powerset, altSum f S) =
          (∑ S ∈ (trueSet y).powerset.filter (fun S => S.card < d), altSum f S) +
          (∑ S ∈ (trueSet y).powerset.filter (fun S => ¬ S.card < d), altSum f S) from
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
  rw [show (∑ S ∈ (trueSet y).powerset.filter (fun S => ¬ S.card < d), altSum f S) = 0 from by
    apply Finset.sum_eq_zero
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset, not_lt] at hS
    exact h_alt_zero S hS.2]
  ring

end PolyDegAltSum

theorem solution
    {n : ℕ} (f : BoolFunc n) (h_pos : 1 ≤ polyDegree f) :
    ∃ S : Finset (Fin n), S.card = polyDegree f ∧
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0 := by
  classical
  set d := polyDegree f with hd_def
  -- The sum in the goal IS Mobius.altSum f S unfolded.
  have h_sum_eq : ∀ S : Finset (Fin n),
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        = Mobius.altSum f S := by
    intro S
    unfold Mobius.altSum Mobius.signR Mobius.realOf Mobius.boolOfFinset
    rfl
  -- Goal becomes: ∃ S, S.card = d ∧ altSum f S ≠ 0.
  rw [show (∃ S : Finset (Fin n), S.card = polyDegree f ∧
            (∑ T ∈ S.powerset,
                (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
                (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0)) ≠ 0)
        ↔ (∃ S : Finset (Fin n), S.card = polyDegree f ∧ Mobius.altSum f S ≠ 0) from by
    apply exists_congr
    intro S
    rw [h_sum_eq S]]
  -- Get a polynomial witness for HasPolyRep f d.
  have h_has_d : HasPolyRep f d := Nat.find_spec _
  obtain ⟨p, hp_td, hp_eval⟩ := h_has_d
  have h_p_eval : ∀ x : Fin n → Bool,
      eval (PolyDegAltSum.realFromBool x) p = Mobius.realOf (f x) := by
    intro x
    show eval (fun i => if x i then (1 : ℝ) else 0) p = _
    rw [hp_eval]
    simp [Mobius.realOf]
  -- Upper bound: altSum f S = 0 for |S| > d.
  have h_upper : ∀ S : Finset (Fin n), d < S.card → Mobius.altSum f S = 0 :=
    fun S hS => PolyDegAltSum.altSum_zero_above_totalDegree f p d hp_td h_p_eval S hS
  -- Lower bound: by contradiction.
  by_contra h_no_witness
  push_neg at h_no_witness
  -- h_no_witness : ∀ S, S.card = d → altSum f S = 0.
  have h_alt_zero : ∀ S : Finset (Fin n), d ≤ S.card → Mobius.altSum f S = 0 := by
    intro S hS
    rcases lt_or_eq_of_le hS with h_lt | h_eq
    · exact h_upper S h_lt
    · exact h_no_witness S h_eq.symm
  -- The contradiction polynomial.
  have h_q := PolyDegAltSum.truncFromAlt_represents f d h_pos h_alt_zero
  have h_q_td := PolyDegAltSum.truncFromAlt_totalDegree_lt f d h_pos
  have h_has_dm1 : HasPolyRep f (d - 1) := by
    refine ⟨PolyDegAltSum.truncFromAlt f d, h_q_td, ?_⟩
    intro x
    have := h_q x
    show eval (fun i => if x i then (1 : ℝ) else 0) _ = _
    have h_real : (fun i => if x i then (1 : ℝ) else 0) = PolyDegAltSum.realFromBool x := rfl
    rw [h_real, this]
    simp [Mobius.realOf]
  -- Contradicts polyDegree f = d.
  have h_min : ¬ HasPolyRep f (d - 1) := by
    have h_lt : d - 1 < polyDegree f := by rw [← hd_def]; omega
    exact Nat.find_min _ h_lt
  exact h_min h_has_dm1
