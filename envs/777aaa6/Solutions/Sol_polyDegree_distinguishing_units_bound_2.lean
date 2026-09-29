-- Prove2me | solution 2 for polyDegree_distinguishing_units_bound
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-09T02:17:33.799139+00:00
-- url     : https://prove2.me/submissions/1589af66-5b13-4f14-990e-e2a1a43d73c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polyDegree_distinguishing_units_bound
import Theorems.Thm_minsky_papert_symmetrization
import Theorems.Thm_markov_brothers_integer_grid_v2
import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-!
# Sketch — `polyDegree_distinguishing_units_bound`

Decomposition of the core combinatorial step in the Nisan-Szegedy proof.
For `g : {0,1}ᵇ → {0,1}` with `g(0) = false` and `g(eᵢ) = true` for every
basis vector, we have `b ≤ 2 · deg(g)²`.

Strategy:
1. Take the polynomial witness `p` realising `g` of total degree ≤ `d`.
2. Apply Minsky-Papert symmetrization to obtain a univariate `Q` of
   `natDegree ≤ d` with `Q(t) · (b choose t) = sum_{|y|=t} eval p y`.
3. Compute `Q(0) = 0` (the only weight-0 vector is the all-false vector).
4. Compute `Q(1) = 1` (every weight-1 vector is some `eᵢ`).
5. Bound `|Q(t)| ≤ 1` for `t ∈ {0,…,b}`.
6. MVT on `[0,1]` gives `c` with `Q'(c) = 1`.
7. Markov's brothers: `|Q'(c)| ≤ 2 d² / b` on `[0,b]`.
8. Combine: `1 ≤ 2 d² / b`, hence `b ≤ 2 d²`.
-/

open MvPolynomial

namespace DistUnits

variable {b : ℕ}

/-- Standard basis vector `eᵢ` of the Boolean cube. -/
def basisVec (i : Fin b) : Fin b → Bool :=
  Function.update (fun _ => false) i true

@[simp] lemma basisVec_self (i : Fin b) : basisVec i i = true := by
  simp [basisVec]

lemma basisVec_other {i j : Fin b} (h : j ≠ i) : basisVec i j = false := by
  simp [basisVec, Function.update_of_ne h]

lemma basisVec_injective : Function.Injective (@basisVec b) := by
  intros i j h
  by_contra hne
  have h1 : basisVec i i = basisVec j i := congrFun h i
  have h2 : basisVec i i = true := basisVec_self i
  have h3 : basisVec j i = false := basisVec_other hne
  rw [h2, h3] at h1
  exact Bool.noConfusion h1

lemma basisVec_filter (i : Fin b) :
    (Finset.univ : Finset (Fin b)).filter (fun j => basisVec i j = true) = {i} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases hji : j = i
  · subst hji; simp
  · rw [basisVec_other hji]; simp [hji]

/-- The set of weight-0 Boolean vectors is the singleton `{const false}`. -/
lemma weight_zero_set :
    ((Finset.univ : Finset (Fin b → Bool)).filter
      (fun y => ((Finset.univ : Finset (Fin b)).filter (fun i => y i = true)).card = 0))
      = {(fun _ => false : Fin b → Bool)} := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, h_card⟩ := hy
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h_card
    rw [Finset.mem_singleton]
    funext i
    have hi_neq : ¬ (y i = true) := h_card (Finset.mem_univ i)
    cases hi : y i
    · rfl
    · exact absurd hi hi_neq
  · intro hy
    rw [Finset.mem_singleton] at hy
    subst hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intros i _
    show ¬ ((false : Bool) = true)
    exact Bool.false_ne_true

/-- The set of weight-1 Boolean vectors equals `image basisVec univ`. -/
lemma weight_one_set :
    ((Finset.univ : Finset (Fin b → Bool)).filter
      (fun y => ((Finset.univ : Finset (Fin b)).filter (fun i => y i = true)).card = 1))
      = (Finset.univ : Finset (Fin b)).image basisVec := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, h_card⟩ := hy
    rw [Finset.card_eq_one] at h_card
    obtain ⟨i, hi⟩ := h_card
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji
      have hj_in : j ∈ ((Finset.univ : Finset (Fin b)).filter (fun k => y k = true)) := by
        rw [hi]; exact Finset.mem_singleton.mpr rfl
      rw [Finset.mem_filter] at hj_in
      rw [basisVec_self]
      exact hj_in.2.symm
    · rw [basisVec_other hji]
      have hj_notin : j ∉ ((Finset.univ : Finset (Fin b)).filter (fun k => y k = true)) := by
        rw [hi]; intro h; exact hji (Finset.mem_singleton.mp h)
      cases hyj : y j
      · rfl
      · exfalso; apply hj_notin
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ j, hyj⟩
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, _, h_eq⟩ := hy
    subst h_eq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [basisVec_filter, Finset.card_singleton]

/-- Cardinality of the weight-`t` set equals `b.choose t`. Bijection
    `y ↦ univ.filter (fun i => y i = true)` to `univ.powersetCard t`. -/
lemma card_weight_eq_choose (t : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter
      (fun y => ((Finset.univ : Finset (Fin b)).filter
                    (fun i => y i = true)).card = t)).card
      = b.choose t := by
  rw [show b.choose t = ((Finset.univ : Finset (Fin b)).powersetCard t).card by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  apply Finset.card_bij
    (fun (y : Fin b → Bool) (_ : y ∈ _) =>
      (Finset.univ : Finset (Fin b)).filter (fun i => y i = true))
  · intros y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hy.2⟩
  · intros y₁ hy₁ y₂ hy₂ heq
    funext i
    have hiff : (i ∈ (Finset.univ : Finset (Fin b)).filter (fun k => y₁ k = true)) ↔
                (i ∈ (Finset.univ : Finset (Fin b)).filter (fun k => y₂ k = true)) := by
      rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiff
    cases h₁ : y₁ i <;> cases h₂ : y₂ i
    · rfl
    · simp [h₁, h₂] at hiff
    · simp [h₁, h₂] at hiff
    · rfl
  · intros S hS
    rw [Finset.mem_powersetCard] at hS
    refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hfilt : (Finset.univ : Finset (Fin b)).filter
                      (fun i => (decide (i ∈ S) : Bool) = true) = S := by
        ext i
        simp
      rw [hfilt]
      exact hS.2
    · ext i
      simp

end DistUnits

open DistUnits

/-! ## Main reduction. -/

theorem solution
    {b : ℕ} (hb : 1 ≤ b) (g : BoolFunc b)
    (h_zero : g (fun _ => false) = false)
    (h_units : ∀ i : Fin b, g (Function.update (fun _ => false) i true) = true) :
    b ≤ 2 * (polyDegree g)^2 := by
  classical
  set d := polyDegree g with hd_def
  -- Step 1: extract the polynomial witness for g at degree d
  have hp : HasPolyRep g d :=
    Nat.find_spec (⟨b, hasPolyRep_card g⟩ : ∃ k, HasPolyRep g k)
  obtain ⟨p, hp_deg, hp_eval⟩ := hp
  -- Step 2: apply Minsky-Papert symmetrization
  obtain ⟨Q, hQ_deg, hQ_sym⟩ := minsky_papert_symmetrization p
  have hQ_deg_d : Q.natDegree ≤ d := hQ_deg.trans hp_deg
  have hb_pos_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos_real
  -- Step 3: Q(0) = 0
  have hQ0 : Q.eval 0 = 0 := by
    have h_sym0 := hQ_sym 0 (Nat.zero_le b)
    have h_choose0 : ((b.choose 0 : ℕ) : ℝ) = 1 := by
      rw [Nat.choose_zero_right]; simp
    rw [Nat.cast_zero] at h_sym0
    rw [h_choose0, mul_one] at h_sym0
    rw [weight_zero_set, Finset.sum_singleton] at h_sym0
    rw [hp_eval (fun _ => false), h_zero] at h_sym0
    simpa using h_sym0
  -- Step 4: Q(1) = 1
  have hQ1 : Q.eval 1 = 1 := by
    have h_sym1 := hQ_sym 1 hb
    have h_choose1 : ((b.choose 1 : ℕ) : ℝ) = (b : ℝ) := by
      rw [Nat.choose_one_right]
    rw [Nat.cast_one] at h_sym1
    rw [h_choose1] at h_sym1
    rw [weight_one_set] at h_sym1
    rw [Finset.sum_image (fun i _ j _ h => basisVec_injective h)] at h_sym1
    have h_each : ∀ i : Fin b,
        MvPolynomial.eval (fun j => if basisVec i j then (1 : ℝ) else 0) p = 1 := by
      intro i
      rw [hp_eval (basisVec i)]
      have hgi : g (basisVec i) = true := by
        unfold basisVec
        exact h_units i
      rw [hgi]
      simp
    rw [Finset.sum_congr rfl (fun i _ => h_each i)] at h_sym1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at h_sym1
    have h_eq : Q.eval 1 * (b : ℝ) = 1 * (b : ℝ) := by rw [h_sym1, one_mul]
    exact mul_right_cancel₀ hb_ne h_eq
  -- Step 5: |Q(t)| ≤ 1 for t ∈ {0,…,b}
  have h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1 := by
    intros t ht
    have h_sym_t := hQ_sym t ht
    have h_card : ((Finset.univ : Finset (Fin b → Bool)).filter
                    (fun y => ((Finset.univ : Finset (Fin b)).filter
                                  (fun i => y i = true)).card = t)).card
                  = b.choose t := card_weight_eq_choose t
    have h_each_bound : ∀ y ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                          (fun y => ((Finset.univ : Finset (Fin b)).filter
                                        (fun i => y i = true)).card = t)),
        |MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p| ≤ 1 := by
      intros y _
      rw [hp_eval y]
      cases h : g y
      · simp
      · simp
    have h_sum_abs_le :
        |∑ y ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)),
            MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p|
        ≤ (b.choose t : ℝ) := by
      have h1 : |∑ y ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)),
                  MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p|
                ≤ ∑ y ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)),
                  |MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ y ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)),
                  |MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p|
                ≤ ∑ _ ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)), (1 : ℝ) :=
        Finset.sum_le_sum h_each_bound
      have h3 : ∑ _ ∈ ((Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t)), (1 : ℝ)
                = (b.choose t : ℝ) := by
        rw [Finset.sum_const, h_card, nsmul_eq_mul, mul_one]
      linarith
    have h_choose_pos : (0 : ℝ) < ((b.choose t : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos ht
    have h_choose_ne : ((b.choose t : ℕ) : ℝ) ≠ 0 := ne_of_gt h_choose_pos
    have h_eq_form : |Q.eval (t : ℝ)| =
        |Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ)| / ((b.choose t : ℕ) : ℝ) := by
      rw [abs_mul, abs_of_pos h_choose_pos,
          mul_div_assoc, div_self h_choose_ne, mul_one]
    rw [h_eq_form, h_sym_t]
    rw [div_le_iff₀ h_choose_pos, one_mul]
    exact h_sum_abs_le
  -- Step 6: directly apply NS Lemma 2 (markov_brothers_integer_grid_v2):
  -- the value constraints Q(0)=0, Q(1)=1 plus the integer-grid bound give b ≤ 2 d²
  -- in one shot, avoiding the false generic continuous-Markov composition.
  exact markov_brothers_integer_grid_v2 hb Q hQ_deg_d hQ0 hQ1 h_bound
