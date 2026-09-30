-- Prove2me | solution 1 for markov_inequality_interval
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:06:52.691261+00:00
-- url     : https://prove2.me/submissions/c935801b-ef3f-4e75-9e1f-734c7fe8188e

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-chebyshev-bounds-unverified-v1.lean" SHA256 d971fb6016dd6f37d41f6262574dfc848e3c2b1665584d8e5ec667ffaa0818d1

/- Uncompiled context-only helper. These are bounds for Chebyshev polynomials,
   not a majorant for arbitrary polynomials and not the full Markov inequality.
   No positive-degree or open-interval assumption is used. -/

set_option autoImplicit false

section

open Polynomial Polynomial.Chebyshev

/-- `|sin (k θ)| ≤ k |sin θ|`, by induction on `k` from the addition formula. -/
theorem MarkovChebyshevBounds.abs_sin_nat_mul_le (k : ℕ) (θ : ℝ) : |Real.sin (k * θ)| ≤ k * |Real.sin θ| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : Real.sin (((k + 1 : ℕ) : ℝ) * θ) =
        Real.sin (k * θ) * Real.cos θ + Real.cos (k * θ) * Real.sin θ := by
      rw [← Real.sin_add]; congr 1; push_cast; ring
    rw [h]
    calc |Real.sin (k * θ) * Real.cos θ + Real.cos (k * θ) * Real.sin θ|
        ≤ |Real.sin (k * θ) * Real.cos θ| + |Real.cos (k * θ) * Real.sin θ| := abs_add_le _ _
      _ = |Real.sin (k * θ)| * |Real.cos θ| + |Real.cos (k * θ)| * |Real.sin θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ |Real.sin (k * θ)| * 1 + 1 * |Real.sin θ| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ k * |Real.sin θ| + |Real.sin θ| := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * |Real.sin θ| := by push_cast; ring

/-- The Chebyshev polynomial of the second kind is bounded by `m + 1` on `[-1, 1]`. -/
theorem MarkovChebyshevBounds.abs_eval_U_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(U ℝ (m : ℤ)).eval x| ≤ (m : ℝ) + 1 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
  have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have hU : (U ℝ (m : ℤ)).eval x * Real.sin (Real.arccos x) =
      Real.sin (((m + 1 : ℕ) : ℝ) * Real.arccos x) := by
    have := U_real_cos (θ := Real.arccos x) (n := (m : ℤ))
    rw [hcos] at this
    rw [this]; push_cast; ring_nf
  have hbound := abs_sin_nat_mul_le (m + 1) (Real.arccos x)
  rcases lt_or_eq_of_le (abs_le.mpr ⟨hx1, hx2⟩) with hlt | heq
  · have hsinpos : 0 < Real.sin (Real.arccos x) := by
      rw [hsin]
      apply Real.sqrt_pos.mpr
      have : x ^ 2 < 1 := by nlinarith [abs_lt.mp hlt]
      linarith
    have key : |(U ℝ (m : ℤ)).eval x| * Real.sin (Real.arccos x) ≤
        ((m : ℝ) + 1) * Real.sin (Real.arccos x) := by
      calc |(U ℝ (m : ℤ)).eval x| * Real.sin (Real.arccos x)
          = |(U ℝ (m : ℤ)).eval x * Real.sin (Real.arccos x)| := by
            rw [abs_mul, abs_of_pos hsinpos]
        _ = |Real.sin (((m + 1 : ℕ) : ℝ) * Real.arccos x)| := by rw [hU]
        _ ≤ ((m + 1 : ℕ) : ℝ) * |Real.sin (Real.arccos x)| := hbound
        _ = ((m : ℝ) + 1) * Real.sin (Real.arccos x) := by
            rw [abs_of_pos hsinpos]; push_cast; ring
    exact le_of_mul_le_mul_right key hsinpos
  · rcases (abs_eq (zero_le_one' ℝ)).mp heq with h1 | h1
    · subst h1
      rw [U_eval_one]; push_cast
      exact le_of_eq (abs_of_nonneg (by positivity))
    · subst h1
      rw [U_eval_neg_one]
      rcases Int.units_eq_one_or ((m : ℤ).negOnePow) with h | h <;> simp [h] <;>
        exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) m],
          by linarith [Nat.cast_nonneg (α := ℝ) m]⟩

theorem MarkovChebyshevBounds.abs_derivative_T_le_sq (n : Nat) {x : Real}
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    |(derivative (T Real (n : Int))).eval x| <= (n : Real) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [T_derivative_eq_U, eval_mul, eval_intCast, abs_mul]
    have h1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [h1]
    have h2 := abs_eval_U_le m hx
    have h3 : |(((m + 1 : ℕ) : ℤ) : ℝ)| = (m : ℝ) + 1 := by
      push_cast; exact abs_of_nonneg (by positivity)
    rw [h3]
    calc ((m : ℝ) + 1) * |(U ℝ (m : ℤ)).eval x| ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((m + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring

theorem MarkovChebyshevBounds.ode_term_T_eq (n : Nat) (x : Real) :
    (x ^ 2 - 1) * (derivative (derivative (T Real (n : Int)))).eval x +
        x * (derivative (T Real (n : Int))).eval x =
      (n : Real) ^ 2 * (T Real (n : Int)).eval x := by
  have hode :
      (1 - x ^ 2) * (derivative (derivative (T Real (n : Int)))).eval x =
        x * (derivative (T Real (n : Int))).eval x -
          (n : Real) ^ 2 * (T Real (n : Int)).eval x := by
    simpa [Function.iterate_succ_apply'] using
      one_sub_X_sq_mul_iterate_derivative_T_eval (R := Real) (n : Int) 0 x
  linear_combination -hode

theorem MarkovChebyshevBounds.abs_ode_term_T_le_sq (n : Nat) {x : Real}
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    |(x ^ 2 - 1) * (derivative (derivative (T Real (n : Int)))).eval x +
        x * (derivative (T Real (n : Int))).eval x| <= (n : Real) ^ 2 := by
  rw [ode_term_T_eq, abs_mul, abs_of_nonneg (sq_nonneg (n : Real))]
  have hT := abs_eval_T_real_le_one (n : Int) (abs_le.mpr (Set.mem_Icc.mp hx))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hT (sq_nonneg (n : Real))

theorem MarkovChebyshevBounds.max_chebyshev_terms_le_sq (n : Nat) {x : Real}
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    max |(derivative (T Real (n : Int))).eval x|
      |(x ^ 2 - 1) * (derivative (derivative (T Real (n : Int)))).eval x +
        x * (derivative (T Real (n : Int))).eval x| <= (n : Real) ^ 2 := by
  exact max_le (abs_derivative_T_le_sq n hx) (abs_ode_term_T_le_sq n hx)

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-chebyshev-bounds-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-endpoint-bounds-unverified-v1.lean" SHA256 fb478bf961075dd717771b8f19e0c11e12e7d4295611b89a75f196d37349bc2b

/- Uncompiled context-only endpoint bounds. No arbitrary interior-point
   derivative inequality is asserted here. -/

set_option autoImplicit false

section

open Polynomial Polynomial.Chebyshev

/-- Lagrange coefficients expressing `P'(1)` through the values of `P` at the Chebyshev nodes. -/
noncomputable def MarkovEndpointBounds.derivC (n : ℕ) (i : ℕ) : ℝ :=
  (∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹ *
    ∑ t ∈ ((Finset.range (n + 1)).erase i).powersetCard (n - 1), ∏ a ∈ t, (1 - node n a)

theorem MarkovEndpointBounds.sumNodes_derivC_eq {n : ℕ} (hn : 1 ≤ n) {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (derivC n) P = P.derivative.eval 1 := by
  have h₁ : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt hP (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  have h₂ : 1 < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]; omega
  have h := Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_node n).injOn h₁ h₂ (1 : ℝ)
  rw [Function.iterate_one] at h
  rw [sumNodes, ← Nat.range_succ_eq_Iic n, h, Nat.factorial_one, Nat.cast_one, one_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.card_range, derivC]
  rw [show n + 1 - (1 + 1) = n - 1 by omega, div_eq_mul_inv]
  ring

theorem MarkovEndpointBounds.negOnePow_mul_derivC_nonneg {n i : ℕ} (hi : i ≤ n) : 0 ≤ (-1) ^ i * derivC n i := by
  rw [derivC, ← mul_assoc]
  refine mul_nonneg ?_ (Finset.sum_nonneg (fun t _ => Finset.prod_nonneg (fun a _ => ?_)))
  · have h := inv_pos.mpr (zero_lt_prod_node_sub_node hi)
    rw [mul_inv, ← inv_pow, inv_neg_one] at h
    exact le_of_lt h
  · have : node n a ≤ 1 := node_mem_Icc.2
    linarith

theorem MarkovEndpointBounds.derivative_at_one_le (P : Polynomial Real) (n : Nat)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) :
    P.derivative.eval 1 <= (n : Real) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hP : P.derivative = 0 := derivative_of_natDegree_zero (Nat.le_zero.mp hdegree)
    simp [hP]
  · have hT : (T ℝ (n : ℤ)).derivative.eval 1 = (n : ℝ) ^ 2 := by
      simpa only [Int.cast_natCast] using derivative_T_eval_one (R := ℝ) (n : ℤ)
    have hTdeg : (T ℝ (n : ℤ)).degree ≤ n := by
      rw [degree_T, Int.natAbs_natCast]
    rw [← hT, ← sumNodes_derivC_eq hn (degree_le_of_natDegree_le hdegree),
      ← sumNodes_derivC_eq hn hTdeg]
    exact sumNodes_le_sumNodes_T (fun i hi => negOnePow_mul_derivC_nonneg hi) hbound

theorem MarkovEndpointBounds.abs_derivative_at_one_le (P : Polynomial Real) (n : Nat)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) :
    |P.derivative.eval 1| <= (n : Real) ^ 2 := by
  have hplus := derivative_at_one_le P n hdegree hbound
  have hnegDegree : (-P).natDegree <= n := by simpa only [natDegree_neg] using hdegree
  have hnegBound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |(-P).eval x| <= 1 := by
    intro x hx
    simpa only [eval_neg, abs_neg] using hbound x hx
  have hminus : -P.derivative.eval 1 <= (n : Real) ^ 2 := by
    simpa only [derivative_neg, eval_neg] using derivative_at_one_le (-P) n hnegDegree hnegBound
  exact abs_le.mpr (And.intro (by linarith) hplus)

theorem MarkovEndpointBounds.abs_derivative_at_neg_one_le (P : Polynomial Real) (n : Nat)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) :
    |P.derivative.eval (-1)| <= (n : Real) ^ 2 := by
  have hreflectDegree : (P.comp (-X)).natDegree <= n := by
    apply natDegree_comp_le.trans
    simpa using hdegree
  have hreflectBound : forall x : Real, Set.Icc (-1 : Real) 1 x ->
      |(P.comp (-X)).eval x| <= 1 := by
    intro x hx
    have hneg : Set.Icc (-1 : Real) 1 (-x) := by
      constructor <;> linarith [hx.1, hx.2]
    simpa only [eval_comp, eval_neg, eval_X] using hbound (-x) hneg
  have h := abs_derivative_at_one_le (P.comp (-X)) n hreflectDegree hreflectBound
  simpa [derivative_comp] using h

theorem MarkovEndpointBounds.abs_derivative_T_at_one (n : Nat) :
    |(T Real (n : Int)).derivative.eval 1| = (n : Real) ^ 2 := by
  simpa only [derivative_T_eval_one, Int.cast_natCast] using abs_of_nonneg (sq_nonneg (n : Real))

theorem MarkovEndpointBounds.abs_derivative_T_at_neg_one (n : Nat) :
    |(T Real (n : Int)).derivative.eval (-1)| = (n : Real) ^ 2 := by
  simp [T_derivative_eq_U, U_eval_neg_one, abs_mul, pow_two]

theorem MarkovEndpointBounds.abs_derivative_at_one_le_T (P : Polynomial Real) (n : Nat)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) :
    |P.derivative.eval 1| <= |(T Real (n : Int)).derivative.eval 1| := by
  rw [abs_derivative_T_at_one]
  exact abs_derivative_at_one_le P n hdegree hbound

theorem MarkovEndpointBounds.abs_derivative_at_neg_one_le_T (P : Polynomial Real) (n : Nat)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) :
    |P.derivative.eval (-1)| <= |(T Real (n : Int)).derivative.eval (-1)| := by
  rw [abs_derivative_T_at_neg_one]
  exact abs_derivative_at_neg_one_le P n hdegree hbound

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-endpoint-bounds-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-degree-unverified-v1.lean" SHA256 8b464b15d43825e29d48ae09edf3d76b27a51dd66169ea8e5fa5ebc53fc273a4

/- Uncompiled context-only degree facts. These do not establish the
   interpolation majorant or any Markov derivative inequality. -/

set_option autoImplicit false

section

open Polynomial Polynomial.Chebyshev

theorem MarkovChebyshevDegree.derivative_degree_lt_of_natDegree_le
    (P : Polynomial Real) (n : Nat) (hdegree : P.natDegree <= n) :
    P.derivative.degree < (n : WithBot Nat) := by
  by_cases hP : P = 0
  · simp [hP]
  · exact (degree_derivative_lt hP).trans_le (degree_le_of_natDegree_le hdegree)

theorem MarkovChebyshevDegree.squared_nat_chebyshev_degree (n : Nat) (hn : 0 < n) :
    (C ((n : Real) ^ 2) * T Real (n : Int)).degree = (n : WithBot Nat) := by
  have hnReal : Not ((n : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsquare : Not ((n : Real) ^ 2 = 0) := pow_ne_zero 2 hnReal
  rw [degree_C_mul hsquare, degree_T]
  simp

theorem MarkovChebyshevDegree.chebyshev_minus_scaled_derivative_degree
    (P : Polynomial Real) (n : Nat) (hn : 0 < n)
    (hdegree : P.natDegree <= n) (scalar : Real) :
    (C ((n : Real) ^ 2) * T Real (n : Int) - C scalar * P.derivative).degree =
      (n : WithBot Nat) := by
  have hright : (C scalar * P.derivative).degree < (n : WithBot Nat) := by
    by_cases hscalar : scalar = 0
    · simp [hscalar]
    · rw [degree_C_mul hscalar]
      exact derivative_degree_lt_of_natDegree_le P n hdegree
  have hleft := squared_nat_chebyshev_degree n hn
  calc
    (C ((n : Real) ^ 2) * T Real (n : Int) - C scalar * P.derivative).degree =
        (C ((n : Real) ^ 2) * T Real (n : Int)).degree :=
      degree_sub_eq_left_of_degree_lt (by simpa only [hleft] using hright)
    _ = (n : WithBot Nat) := hleft

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-degree-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-rescaling-unverified-v2.lean" SHA256 07faa552098dd1b34812b7814a04eab41b0d6001d7d40714ade338395c4f1db0

/- Uncompiled context-only reduction. The normalized Markov inequality is an
   explicit hypothesis, not a proved result. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial

def MarkovIntervalRescaling.NormalizedMarkov : Prop :=
  forall (P : Polynomial Real) (n : Nat), 0 < n -> P.natDegree <= n ->
    (forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= 1) ->
    forall x : Real, Set.Icc (-1 : Real) 1 x ->
      |P.derivative.eval x| <= (n : Real) ^ 2

def MarkovIntervalRescaling.affine (a b : Real) : Polynomial Real :=
  C ((b - a) / 2) * X + C ((a + b) / 2)

theorem MarkovIntervalRescaling.natDegree_affine_le (a b : Real) : (affine a b).natDegree <= 1 := by
  unfold affine
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le ((b - a) / 2) X).trans natDegree_X_le
  · simp

theorem MarkovIntervalRescaling.derivative_affine (a b : Real) :
    derivative (affine a b) = C ((b - a) / 2) := by
  simp [affine, derivative_add]

theorem MarkovIntervalRescaling.affine_mem_Icc (a b : Real) (hab : a < b) {x : Real}
    (hx : Set.Icc (-1 : Real) 1 x) : Set.Icc a b ((affine a b).eval x) := by
  have hwidth : 0 < (b - a) / 2 := half_pos (sub_pos.mpr hab)
  have hlo := mul_le_mul_of_nonneg_left hx.1 hwidth.le
  have hhi := mul_le_mul_of_nonneg_left hx.2 hwidth.le
  simp only [affine, eval_add, eval_mul, eval_C, eval_X]
  constructor <;> nlinarith

theorem MarkovIntervalRescaling.inverse_parameter_mem_Icc (a b c : Real) (hab : a < b)
    (hac : a <= c) (hcb : c <= b) :
    Set.Icc (-1 : Real) 1 ((2 * c - a - b) / (b - a)) := by
  have hwidth : 0 < b - a := sub_pos.mpr hab
  constructor
  · apply (le_div_iff₀ hwidth).2
    linarith
  · apply (div_le_iff₀ hwidth).2
    linarith

theorem MarkovIntervalRescaling.affine_eval_inverse_parameter (a b c : Real) (hab : a < b) :
    (affine a b).eval ((2 * c - a - b) / (b - a)) = c := by
  have hwidth : Not (b - a = 0) := ne_of_gt (sub_pos.mpr hab)
  simp only [affine, eval_add, eval_mul, eval_C, eval_X]
  field_simp [hwidth]; ring

theorem MarkovIntervalRescaling.derivative_comp_affine_eval (Q : Polynomial Real) (a b x : Real) :
    (Q.comp (affine a b)).derivative.eval x =
      ((b - a) / 2) * Q.derivative.eval ((affine a b).eval x) := by
  simp only [derivative_comp, derivative_affine, eval_mul, eval_C, eval_comp]

theorem MarkovIntervalRescaling.eq_zero_of_interval_bound_zero (Q : Polynomial Real) (a b : Real)
    (hab : a < b)
    (hbound : forall x : Real, a <= x -> x <= b -> |Q.eval x| <= 0) : Q = 0 := by
  apply Q.eq_zero_of_infinite_isRoot
  apply (Set.Icc_infinite hab).mono
  intro x hx
  show Q.eval x = 0
  exact abs_eq_zero.mp (le_antisymm (hbound x hx.1 hx.2) (abs_nonneg _))

theorem MarkovIntervalRescaling.positive_scale_bound (hmarkov : NormalizedMarkov)
    (P : Polynomial Real) (n : Nat) (hn : 0 < n) (M : Real) (hM : 0 < M)
    (hdegree : P.natDegree <= n)
    (hbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= M)
    (x : Real) (hx : Set.Icc (-1 : Real) 1 x) :
    |P.derivative.eval x| <= (n : Real) ^ 2 * M := by
  let R : Polynomial Real := C (1 / M) * P
  have hRdegree : R.natDegree <= n :=
    (natDegree_C_mul_le (1 / M) P).trans hdegree
  have hreciprocal : 0 < 1 / M := one_div_pos.mpr hM
  have hRbound : forall t : Real, Set.Icc (-1 : Real) 1 t -> |R.eval t| <= 1 := by
    intro t ht
    simp only [R, eval_mul, eval_C, abs_mul, abs_of_pos hreciprocal]
    calc
      (1 / M) * |P.eval t| <= (1 / M) * M :=
        mul_le_mul_of_nonneg_left (hbound t ht) hreciprocal.le
      _ = 1 := by field_simp [ne_of_gt hM]
  have hnormalized := hmarkov R n hn hRdegree hRbound x hx
  have hscaled : (1 / M) * |P.derivative.eval x| <= (n : Real) ^ 2 := by
    simpa only [R, derivative_C_mul, eval_mul, eval_C, abs_mul, abs_of_pos hreciprocal]
      using hnormalized
  calc
    |P.derivative.eval x| = M * ((1 / M) * |P.derivative.eval x|) := by
      field_simp [ne_of_gt hM]
    _ <= M * (n : Real) ^ 2 := mul_le_mul_of_nonneg_left hscaled hM.le
    _ = (n : Real) ^ 2 * M := mul_comm _ _

theorem MarkovIntervalRescaling.interval_bound_of_normalized (hmarkov : NormalizedMarkov)
    (a b : Real) (hab : a < b) (Q : Polynomial Real) {d : Nat} (M : Real)
    (h_deg : Q.natDegree <= d)
    (h_bound : forall x : Real, a <= x -> x <= b -> |Q.eval x| <= M) :
    forall c : Real, a <= c -> c <= b ->
      |Q.derivative.eval c| <= 2 * (d : Real) ^ 2 * M / (b - a) := by
  intro c hac hcb
  by_cases hd : d = 0
  · subst d
    have hQ : Q.derivative = 0 := derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero h_deg)
    simp [hQ]
  have hMnonneg : 0 <= M := (abs_nonneg (Q.eval a)).trans (h_bound a le_rfl hab.le)
  rcases eq_or_lt_of_le hMnonneg with hMzero | hM
  · have hMzero' : M = 0 := hMzero.symm
    subst M
    have hQ := eq_zero_of_interval_bound_zero Q a b hab h_bound
    simp [hQ]
  let P : Polynomial Real := Q.comp (affine a b)
  have hPdegree : P.natDegree <= d := by
    calc
      P.natDegree <= Q.natDegree * (affine a b).natDegree := natDegree_comp_le
      _ <= Q.natDegree * 1 := Nat.mul_le_mul_left _ (natDegree_affine_le a b)
      _ <= d := by simpa only [Nat.mul_one] using h_deg
  have hPbound : forall x : Real, Set.Icc (-1 : Real) 1 x -> |P.eval x| <= M := by
    intro x hx
    have hy := affine_mem_Icc a b hab hx
    simpa only [P, eval_comp] using h_bound ((affine a b).eval x) hy.1 hy.2
  let t : Real := (2 * c - a - b) / (b - a)
  have ht : Set.Icc (-1 : Real) 1 t := inverse_parameter_mem_Icc a b c hab hac hcb
  have hscale := positive_scale_bound hmarkov P d (Nat.pos_of_ne_zero hd) M hM hPdegree hPbound t ht
  have hderivative : P.derivative.eval t = ((b - a) / 2) * Q.derivative.eval c := by
    dsimp only [P, t]
    rw [derivative_comp_affine_eval, affine_eval_inverse_parameter a b c hab]
  have hwidth : 0 < b - a := sub_pos.mpr hab
  rw [hderivative, abs_mul, abs_of_pos (half_pos hwidth)] at hscale
  apply (le_div_iff₀ hwidth).2
  nlinarith [hscale]

end

end


-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-rescaling-unverified-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-root-count-work-v2.lean" SHA256 adc47a0866753100a16976eac7c4435246795288592714e3e936c9ea69d1e08b

section

open Polynomial Set

private theorem ShadrinRootCount.abs_mul_lt_of_dom {a b t : ℝ} (ht : |t| < 1)
    (ha : a ≠ 0) (hdom : |b| ≤ |a|) : |t * b| < |a| := by
  rw [abs_mul]
  calc
    |t| * |b| ≤ |t| * |a| := mul_le_mul_of_nonneg_left hdom (abs_nonneg t)
    _ < 1 * |a| := mul_lt_mul_of_pos_right ht (abs_pos.mpr ha)
    _ = |a| := one_mul _

private theorem ShadrinRootCount.sub_mul_pos {a b t : ℝ} (ht : |t| < 1)
    (ha : 0 < a) (hdom : |b| ≤ |a|) : 0 < a - t * b := by
  have hsmall := abs_mul_lt_of_dom ht ha.ne' hdom
  rw [abs_of_pos ha] at hsmall
  have hupper := le_abs_self (t * b)
  linarith

private theorem ShadrinRootCount.sub_mul_neg {a b t : ℝ} (ht : |t| < 1)
    (ha : a < 0) (hdom : |b| ≤ |a|) : a - t * b < 0 := by
  have hsmall := abs_mul_lt_of_dom ht ha.ne hdom
  rw [abs_of_neg ha] at hsmall
  have hlower := neg_abs_le (t * b)
  linarith

theorem ShadrinRootCount.abs_eval_le_of_ordered_intervals
    {n : ℕ} (r s : ℝ[X]) (left right : Fin n → ℝ)
    (hr : r.degree = (n : WithBot ℕ))
    (hs : s.degree < (n : WithBot ℕ))
    (hinterval : ∀ i, left i < right i)
    (hordered : ∀ i j, i < j → right i ≤ left j)
    (hsign : ∀ i,
      (r.eval (left i) < 0 ∧ 0 < r.eval (right i)) ∨
      (0 < r.eval (left i) ∧ r.eval (right i) < 0))
    (hdom : ∀ i,
      |s.eval (left i)| ≤ |r.eval (left i)| ∧
      |s.eval (right i)| ≤ |r.eval (right i)|)
    (x : ℝ) (hx : ∀ i, x ∉ Ioo (left i) (right i)) :
    |s.eval x| ≤ |r.eval x| := by
  classical
  by_contra hbound
  have hbad : |r.eval x| < |s.eval x| := lt_of_not_ge hbound
  have hsx : s.eval x ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hbad
    exact (not_lt_of_ge (abs_nonneg (r.eval x))) hbad
  let t : ℝ := r.eval x / s.eval x
  have ht : |t| < 1 := by
    dsimp [t]
    rw [abs_div]
    exact (div_lt_one (abs_pos.mpr hsx)).mpr hbad
  let H : ℝ[X] := r - C t * s
  have hHx : H.eval x = 0 := by
    simp only [H, eval_sub, eval_mul, eval_C]
    dsimp [t]
    rw [div_mul_cancel₀ _ hsx, sub_self]
  have hscaled : (C t * s).degree < r.degree := by
    have hle : (C t * s).degree ≤ s.degree := by
      calc
        (C t * s).degree ≤ (0 : WithBot ℕ) + s.degree :=
          degree_mul_le_of_le degree_C_le le_rfl
        _ = s.degree := zero_add _
    rw [hr]
    exact hle.trans_lt hs
  have hHdegree : H.degree = (n : WithBot ℕ) :=
    (degree_sub_eq_left_of_degree_lt hscaled).trans hr
  have hHnatDegree : H.natDegree = n :=
    natDegree_eq_of_degree_eq_some hHdegree

  have hroots : ∀ i, ∃ z ∈ Ioo (left i) (right i), H.eval z = 0 := by
    intro i
    rcases hsign i with hsigni | hsigni
    · have hleft : H.eval (left i) < 0 := by
        simpa only [H, eval_sub, eval_mul, eval_C] using
          sub_mul_neg ht hsigni.1 (hdom i).1
      have hright : 0 < H.eval (right i) := by
        simpa only [H, eval_sub, eval_mul, eval_C] using
          sub_mul_pos ht hsigni.2 (hdom i).2
      exact intermediate_value_Ioo (hinterval i).le H.continuousOn ⟨hleft, hright⟩
    · have hleft : 0 < H.eval (left i) := by
        simpa only [H, eval_sub, eval_mul, eval_C] using
          sub_mul_pos ht hsigni.1 (hdom i).1
      have hright : H.eval (right i) < 0 := by
        simpa only [H, eval_sub, eval_mul, eval_C] using
          sub_mul_neg ht hsigni.2 (hdom i).2
      exact intermediate_value_Ioo' (hinterval i).le H.continuousOn ⟨hright, hleft⟩

  let z : Fin n → ℝ := fun i => Classical.choose (hroots i)
  have hzmem : ∀ i, z i ∈ Ioo (left i) (right i) :=
    fun i => (Classical.choose_spec (hroots i)).1
  have hzeval : ∀ i, H.eval (z i) = 0 :=
    fun i => (Classical.choose_spec (hroots i)).2
  have hzmono : StrictMono z := by
    intro i j hij
    exact ((hzmem i).2.trans_le (hordered i j hij)).trans (hzmem j).1

  let points : Option (Fin n) → ℝ
    | none => x
    | some i => z i
  have hinjective : Function.Injective points := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some j =>
            change x = z j at hab
            exact (hx j (hab.symm ▸ hzmem j)).elim
    | some i =>
        cases b with
        | none =>
            change z i = x at hab
            exact (hx i (hab ▸ hzmem i)).elim
        | some j =>
            change z i = z j at hab
            exact congrArg Option.some (hzmono.injective hab)
  have hpoints : ∀ u, H.eval (points u) = 0 := by
    intro u
    cases u with
    | none => exact hHx
    | some i => exact hzeval i
  have hHzero : H = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero H hinjective hpoints
      (by simp [hHnatDegree])
  simp [hHzero] at hHdegree

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-root-count-work-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-sign-intervals-v1.lean" SHA256 3a39a17498eb184f0410f634ed86ddbba483a38f0d4ec6dfa74f1cbaf5364539

set_option autoImplicit false

section

open Polynomial Set

theorem MarkovSignIntervals.roots_exhausted {n : Nat} (p : Polynomial Real) (z : Fin n -> Real)
    (hdegree : p.degree = (n : WithBot Nat))
    (hinjective : Function.Injective z) (hroots : forall i, p.eval (z i) = 0)
    (x : Real) (hx : p.eval x = 0) : ∃ i, x = z i := by
  classical
  by_contra hmissing
  have havoid : forall i, ¬ x = z i := by
    intro i hi
    exact hmissing (Exists.intro i hi)
  let points : Option (Fin n) -> Real
    | none => x
    | some i => z i
  have hpoints_injective : Function.Injective points := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some j => exact (havoid j hab).elim
    | some i =>
        cases b with
        | none => exact (havoid i hab.symm).elim
        | some j => exact congrArg Option.some (hinjective hab)
  have hpoints_root : forall u, p.eval (points u) = 0 := by
    intro u
    cases u with
    | none => exact hx
    | some i => exact hroots i
  have hnatDegree : p.natDegree = n := natDegree_eq_of_degree_eq_some hdegree
  have hzero : p = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    hpoints_injective hpoints_root (by simp [hnatDegree])
  simp [hzero] at hdegree

theorem MarkovSignIntervals.nonneg_on_closed_of_no_zero (f : Real -> Real) {a b z : Real}
    (hcontinuous : Continuous f) (hz : z ∈ Ioo a b) (hpositive : 0 < f z)
    (hnozero : ∀ y ∈ Ioo a b, ¬ f y = 0) :
    ∀ x ∈ Icc a b, 0 <= f x := by
  intro x hx
  by_contra hnonneg
  have hnegative : f x < 0 := lt_of_not_ge hnonneg
  rcases lt_trichotomy x z with hlt | heq | hgt
  · obtain ⟨y, hy, hyzero⟩ := intermediate_value_Ioo hlt.le
      hcontinuous.continuousOn ⟨hnegative, hpositive⟩
    exact hnozero y ⟨hx.1.trans_lt hy.1, hy.2.trans hz.2⟩ hyzero
  · exact (not_lt_of_ge hpositive.le) (heq ▸ hnegative)
  · obtain ⟨y, hy, hyzero⟩ := intermediate_value_Ioo' hgt.le
      hcontinuous.continuousOn ⟨hnegative, hpositive⟩
    exact hnozero y ⟨hz.1.trans hy.1, hy.2.trans_le hx.2⟩ hyzero

theorem MarkovSignIntervals.signed_nonneg_on_closed (p : Polynomial Real) (sign : Real)
    {a b z : Real} (hz : z ∈ Ioo a b) (hpositive : 0 < sign * p.eval z)
    (hnozero : ∀ y ∈ Ioo a b, ¬ p.eval y = 0) :
    ∀ x ∈ Icc a b, 0 <= sign * p.eval x := by
  have hsign : ¬ sign = 0 := by
    intro heq
    simp [heq] at hpositive
  exact nonneg_on_closed_of_no_zero (fun x => sign * p.eval x)
    (continuous_const.mul p.continuous) hz hpositive
    (fun y hy => mul_ne_zero hsign (hnozero y hy))

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-sign-intervals-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-nodal-factor-v1.lean" SHA256 7ee447300cae9210f5e153b55b4101af103ec5e5e08ecdce5e6bd3bb0071fd2f

set_option autoImplicit false

noncomputable section

section

open Polynomial

theorem MarkovNodalFactor.eq_leadingCoeff_mul_nodal {I : Type*} (s : Finset I) (tau : I -> Real)
    (p : Polynomial Real) (hinjective : Set.InjOn tau s)
    (hdegree : p.degree = (s.card : WithBot Nat))
    (hroots : ∀ i ∈ s, p.eval (tau i) = 0) :
    p = C p.leadingCoeff * Lagrange.nodal s tau := by
  have hp : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdegree
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  apply eq_of_degree_le_of_eval_index_eq s hinjective
  · exact hdegree.le
  · rw [degree_C_mul hlc, Lagrange.degree_nodal, hdegree]
  · rw [leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff, mul_one]
  · intro i hi
    rw [hroots i hi, eval_mul, eval_C, Lagrange.eval_nodal_at_node hi, mul_zero]

theorem MarkovNodalFactor.deleted_factor_eq {I : Type*} [DecidableEq I]
    (s : Finset I) (tau : I -> Real) (p q : Polynomial Real)
    (hinjective : Set.InjOn tau s)
    (hdegree : p.degree = (s.card : WithBot Nat))
    (hroots : ∀ i ∈ s, p.eval (tau i) = 0)
    (i : I) (hi : i ∈ s) (hfactor : p = (X - C (tau i)) * q) :
    q = C p.leadingCoeff * Lagrange.nodal (s.erase i) tau := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero (tau i))
  calc
    (X - C (tau i)) * q = p := hfactor.symm
    _ = C p.leadingCoeff * Lagrange.nodal s tau :=
      eq_leadingCoeff_mul_nodal s tau p hinjective hdegree hroots
    _ = (X - C (tau i)) * (C p.leadingCoeff * Lagrange.nodal (s.erase i) tau) := by
      rw [Lagrange.nodal_eq_mul_nodal_erase hi]
      ring

theorem MarkovNodalFactor.deleted_derivative_orientation {I : Type*} [DecidableEq I]
    (s : Finset I) (tau : I -> Real) (p q : Polynomial Real)
    (hinjective : Set.InjOn tau s)
    (hdegree : p.degree = (s.card : WithBot Nat))
    (hroots : ∀ i ∈ s, p.eval (tau i) = 0)
    (i : I) (hi : i ∈ s) (hfactor : p = (X - C (tau i)) * q)
    (hlc : 0 < p.leadingCoeff) (x sign : Real)
    (horientation : 0 <= sign * q.derivative.eval x) :
    0 <= sign * (Lagrange.nodal (s.erase i) tau).derivative.eval x := by
  rw [deleted_factor_eq s tau p q hinjective hdegree hroots i hi hfactor,
    derivative_C_mul, eval_mul, eval_C] at horientation
  have hscaled : 0 <= p.leadingCoeff *
      (sign * (Lagrange.nodal (s.erase i) tau).derivative.eval x) := by
    simpa only [mul_left_comm] using horientation
  by_contra hnegative
  exact (not_lt_of_ge hscaled)
    (mul_neg_of_pos_of_neg hlc (lt_of_not_ge hnegative))

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-nodal-factor-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-deleted-orientation-unverified-v2.lean" SHA256 2975aa7bc6a4dfbae9f94cbe8bf3f2b56c06218607d0821f7ba29aededac3335

/- Uncompiled algebraic draft, not a Markov or Shadrin majorant proof.
   A sign parameter covers either weak orientation: use sign = 1 for
   nonnegative derivatives and sign = -1 for nonpositive derivatives.
   The final theorem explicitly excludes every interpolation node. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial

theorem MarkovDeletedOrientation.deleted_derivative_identity (omega q : Polynomial Real) (t x : Real)
    (hfactor : omega = (X - C t) * q) :
    (x - t) ^ 2 * (derivative q).eval x =
      (x - t) * (derivative omega).eval x - omega.eval x := by
  rw [hfactor, derivative_mul, derivative_X_sub_C]
  simp only [one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  ring

theorem MarkovDeletedOrientation.numerator_affine (t x value slope : Real) :
    (x - t) * slope - value =
      ((1 - t) / 2) * ((x + 1) * slope - value) +
        ((1 + t) / 2) * ((x - 1) * slope - value) := by
  ring

theorem MarkovDeletedOrientation.numerator_orientation (t x value slope sign : Real)
    (ht : t ∈ Set.Icc (-1 : Real) 1)
    (hleft : 0 <= sign * ((x + 1) * slope - value))
    (hright : 0 <= sign * ((x - 1) * slope - value)) :
    0 <= sign * ((x - t) * slope - value) := by
  have hleftWeight : 0 <= (1 - t) / 2 := by
    linarith [ht.2]
  have hrightWeight : 0 <= (1 + t) / 2 := by
    linarith [ht.1]
  calc
    0 <= ((1 - t) / 2) * (sign * ((x + 1) * slope - value)) +
        ((1 + t) / 2) * (sign * ((x - 1) * slope - value)) :=
      add_nonneg (mul_nonneg hleftWeight hleft) (mul_nonneg hrightWeight hright)
    _ = sign * ((x - t) * slope - value) := by
      rw [numerator_affine t x value slope]
      ring

theorem MarkovDeletedOrientation.factor_derivative_orientation
    (omega qLeft qRight q : Polynomial Real) (t x sign : Real)
    (hleftFactor : omega = (X - C (-1)) * qLeft)
    (hrightFactor : omega = (X - C 1) * qRight)
    (hfactor : omega = (X - C t) * q)
    (ht : t ∈ Set.Icc (-1 : Real) 1) (hx : x ≠ t)
    (hleft : 0 <= sign * (derivative qLeft).eval x)
    (hright : 0 <= sign * (derivative qRight).eval x) :
    0 <= sign * (derivative q).eval x := by
  have hleftIdentity :
      (x + 1) ^ 2 * (derivative qLeft).eval x =
        (x + 1) * (derivative omega).eval x - omega.eval x := by
    simpa only [sub_neg_eq_add] using
      deleted_derivative_identity omega qLeft (-1) x hleftFactor
  have hrightIdentity := deleted_derivative_identity omega qRight 1 x hrightFactor
  have hleftNumerator :
      0 <= sign * ((x + 1) * (derivative omega).eval x - omega.eval x) := by
    rw [← hleftIdentity]
    calc
      0 <= (x + 1) ^ 2 * (sign * (derivative qLeft).eval x) :=
        mul_nonneg (sq_nonneg (x + 1)) hleft
      _ = sign * ((x + 1) ^ 2 * (derivative qLeft).eval x) := by ring
  have hrightNumerator :
      0 <= sign * ((x - 1) * (derivative omega).eval x - omega.eval x) := by
    rw [← hrightIdentity]
    calc
      0 <= (x - 1) ^ 2 * (sign * (derivative qRight).eval x) :=
        mul_nonneg (sq_nonneg (x - 1)) hright
      _ = sign * ((x - 1) ^ 2 * (derivative qRight).eval x) := by ring
  have hnumerator := numerator_orientation t x (omega.eval x)
    ((derivative omega).eval x) sign ht hleftNumerator hrightNumerator
  have hidentity := deleted_derivative_identity omega q t x hfactor
  have hscaled : 0 <= (x - t) ^ 2 * (sign * (derivative q).eval x) := by
    calc
      0 <= sign * ((x - t) * (derivative omega).eval x - omega.eval x) := hnumerator
      _ = sign * ((x - t) ^ 2 * (derivative q).eval x) := by rw [hidentity]
      _ = (x - t) ^ 2 * (sign * (derivative q).eval x) := by ring
  have hsquare : 0 < (x - t) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  by_contra hnegative
  exact (not_lt_of_ge hscaled)
    (mul_neg_of_pos_of_neg hsquare (lt_of_not_ge hnegative))

def MarkovDeletedOrientation.nodeProduct {I : Type*} (nodes : Finset I) (tau : I -> Real) : Polynomial Real :=
  nodes.prod (fun i => X - C (tau i))

def MarkovDeletedOrientation.deletedProduct {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (i : I) : Polynomial Real :=
  nodeProduct (nodes.erase i) tau

theorem MarkovDeletedOrientation.nodeProduct_factor {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) {i : I} (hi : i ∈ nodes) :
    nodeProduct nodes tau = (X - C (tau i)) * deletedProduct nodes tau i := by
  exact (Finset.mul_prod_erase nodes (fun j => (X - C (tau j) : Polynomial Real)) hi).symm

theorem MarkovDeletedOrientation.all_deleted_derivatives_orientation {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (left right : I)
    (hleftMem : left ∈ nodes) (hrightMem : right ∈ nodes)
    (hleftNode : tau left = -1) (hrightNode : tau right = 1)
    (hnodes : ∀ i ∈ nodes, tau i ∈ Set.Icc (-1 : Real) 1)
    (x sign : Real) (havoid : ∀ i ∈ nodes, x ≠ tau i)
    (hleft : 0 <= sign * (derivative (deletedProduct nodes tau left)).eval x)
    (hright : 0 <= sign * (derivative (deletedProduct nodes tau right)).eval x) :
    ∀ i ∈ nodes, 0 <= sign * (derivative (deletedProduct nodes tau i)).eval x := by
  intro i hi
  have hleftFactor : nodeProduct nodes tau =
      (X - C (-1)) * deletedProduct nodes tau left := by
    simpa only [hleftNode] using nodeProduct_factor nodes tau hleftMem
  have hrightFactor : nodeProduct nodes tau =
      (X - C 1) * deletedProduct nodes tau right := by
    simpa only [hrightNode] using nodeProduct_factor nodes tau hrightMem
  exact factor_derivative_orientation (nodeProduct nodes tau)
    (deletedProduct nodes tau left) (deletedProduct nodes tau right)
    (deletedProduct nodes tau i) (tau i) x sign hleftFactor hrightFactor
    (nodeProduct_factor nodes tau hi) (hnodes i hi) (havoid i hi) hleft hright

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-deleted-orientation-unverified-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-lagrange-unverified-v4.lean" SHA256 f69e18353c45411bf238a0f18250a2943f4a9e225fa79af47cab557638d34b0d

/- Uncompiled interpolation helper, not the full Markov/Shadrin majorant.
   deletedPolynomial is definitionally equal to the deletedProduct in the
   separate orientation draft. Its common-sign conclusion supplies hcommon.
   The coefficient-sign premise intentionally leaves node-order alternation
   unproved. Two unit signs allow either global extremal phase/orientation. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial
open scoped BigOperators

def MarkovLagrange.denominator {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (i : I) : Real :=
  (nodes.erase i).prod (fun j => tau i - tau j)

def MarkovLagrange.deletedPolynomial {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (i : I) : Polynomial Real :=
  (nodes.erase i).prod (fun j => X - C (tau j))

theorem MarkovLagrange.deletedPolynomial_eval_node {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (i : I) :
    (deletedPolynomial nodes tau i).eval (tau i) = denominator nodes tau i := by
  simp only [deletedPolynomial, denominator, eval_prod, eval_sub, eval_X, eval_C]

theorem MarkovLagrange.denominator_ne_zero {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (hinj : Set.InjOn tau (nodes : Set I))
    {i : I} (hi : i ∈ nodes) : denominator nodes tau i ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro heq
  exact (Finset.mem_erase.mp hj).1
    ((hinj hi (Finset.mem_erase.mp hj).2 heq).symm)

theorem MarkovLagrange.derivative_eval_eq_sum {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (hinj : Set.InjOn tau (nodes : Set I))
    (P : Polynomial Real) (hP : P.degree < nodes.card) (x : Real) :
    (derivative P).eval x =
      ∑ i ∈ nodes, (P.eval (tau i) / denominator nodes tau i) *
        (derivative (deletedPolynomial nodes tau i)).eval x := by
  have hpoly : P = ∑ i ∈ nodes,
      C (P.eval (tau i) / denominator nodes tau i) * deletedPolynomial nodes tau i := by
    calc
      P = Lagrange.interpolate nodes tau (fun i => P.eval (tau i)) :=
        Lagrange.eq_interpolate hinj hP
      _ = ∑ i ∈ nodes,
          C (P.eval (tau i) / denominator nodes tau i) * deletedPolynomial nodes tau i := by
        simpa only [denominator, deletedPolynomial] using
          (Lagrange.interpolate_eq_sum (s := nodes) (v := tau) (fun i => P.eval (tau i)))
  have h := congrArg (fun R : Polynomial Real => (derivative R).eval x) hpoly
  simpa only [derivative_sum, derivative_C_mul, eval_finset_sum, eval_mul, eval_C] using h

theorem MarkovLagrange.abs_sum_le_abs_sum_of_sign {I : Type*}
    (nodes : Finset I) (a b weight : I -> Real) (sign : Real)
    (hsign : |sign| = 1)
    (ha : ∀ i ∈ nodes, |a i| <= 1)
    (hb : ∀ i ∈ nodes, |b i| = 1)
    (hcommon : ∀ i ∈ nodes, 0 <= sign * (b i * weight i)) :
    |∑ i ∈ nodes, a i * weight i| <= |∑ i ∈ nodes, b i * weight i| := by
  have hweight (i : I) (hi : i ∈ nodes) : |weight i| = sign * (b i * weight i) := by
    calc
      |weight i| = |sign * (b i * weight i)| := by
        simp only [abs_mul, hsign, hb i hi, one_mul]
      _ = sign * (b i * weight i) := abs_of_nonneg (hcommon i hi)
  have hsum : (∑ i ∈ nodes, |weight i|) = sign * ∑ i ∈ nodes, b i * weight i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hweight i hi)
  calc
    |∑ i ∈ nodes, a i * weight i| <= ∑ i ∈ nodes, |a i * weight i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ nodes, |weight i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |a i| * |weight i| <= 1 * |weight i| :=
          mul_le_mul_of_nonneg_right (ha i hi) (abs_nonneg (weight i))
        _ = |weight i| := one_mul _
    _ = sign * ∑ i ∈ nodes, b i * weight i := hsum
    _ <= |sign * ∑ i ∈ nodes, b i * weight i| := le_abs_self _
    _ = |∑ i ∈ nodes, b i * weight i| := by rw [abs_mul, hsign, one_mul]

theorem MarkovLagrange.derivative_bound_of_coefficient_sign {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (hinj : Set.InjOn tau (nodes : Set I))
    (P Q : Polynomial Real) (hP : P.degree < nodes.card) (hQ : Q.degree < nodes.card)
    (x coefficientSign derivativeSign : Real)
    (hcoefficientSign : |coefficientSign| = 1) (hderivativeSign : |derivativeSign| = 1)
    (hbounded : ∀ i ∈ nodes, |P.eval (tau i)| <= 1)
    (hextremal : ∀ i ∈ nodes, |Q.eval (tau i)| = 1)
    (hcoefficient : ∀ i ∈ nodes,
      0 <= coefficientSign * (Q.eval (tau i) / denominator nodes tau i))
    (hcommon : ∀ i ∈ nodes,
      0 <= derivativeSign * (derivative (deletedPolynomial nodes tau i)).eval x) :
    |(derivative P).eval x| <= |(derivative Q).eval x| := by
  let weight : I -> Real := fun i =>
    (denominator nodes tau i)⁻¹ * (derivative (deletedPolynomial nodes tau i)).eval x
  have hsign : |coefficientSign * derivativeSign| = 1 := by
    rw [abs_mul, hcoefficientSign, hderivativeSign, one_mul]
  have hcombined : ∀ i ∈ nodes,
      0 <= (coefficientSign * derivativeSign) * (Q.eval (tau i) * weight i) := by
    intro i hi
    calc
      0 <= (coefficientSign * (Q.eval (tau i) / denominator nodes tau i)) *
          (derivativeSign * (derivative (deletedPolynomial nodes tau i)).eval x) :=
        mul_nonneg (hcoefficient i hi) (hcommon i hi)
      _ = (coefficientSign * derivativeSign) * (Q.eval (tau i) * weight i) := by
        dsimp [weight]
        rw [div_eq_mul_inv]
        ring
  have hformula (R : Polynomial Real) (hR : R.degree < nodes.card) :
      (derivative R).eval x = ∑ i ∈ nodes, R.eval (tau i) * weight i := by
    rw [derivative_eval_eq_sum nodes tau hinj R hR x]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [weight]
    rw [div_eq_mul_inv]
    ring
  rw [hformula P hP, hformula Q hQ]
  exact abs_sum_le_abs_sum_of_sign nodes (fun i => P.eval (tau i))
    (fun i => Q.eval (tau i)) weight (coefficientSign * derivativeSign)
    hsign hbounded hextremal hcombined

theorem MarkovLagrange.derivative_bound_fin (n : Nat) (tau : Fin (n + 1) -> Real)
    (hinj : Function.Injective tau) (P Q : Polynomial Real)
    (hP : P.natDegree <= n) (hQ : Q.natDegree <= n)
    (x coefficientSign derivativeSign : Real)
    (hcoefficientSign : |coefficientSign| = 1) (hderivativeSign : |derivativeSign| = 1)
    (hbounded : ∀ i, |P.eval (tau i)| <= 1)
    (hextremal : ∀ i, |Q.eval (tau i)| = 1)
    (hcoefficient : ∀ i,
      0 <= coefficientSign * (Q.eval (tau i) / denominator Finset.univ tau i))
    (hcommon : ∀ i,
      0 <= derivativeSign * (derivative (deletedPolynomial Finset.univ tau i)).eval x) :
    |(derivative P).eval x| <= |(derivative Q).eval x| := by
  have hPdegree : P.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le hP) ?_
    exact_mod_cast (Nat.lt_succ_self n)
  have hQdegree : Q.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le hQ) ?_
    exact_mod_cast (Nat.lt_succ_self n)
  exact derivative_bound_of_coefficient_sign Finset.univ tau hinj.injOn P Q
    hPdegree hQdegree x coefficientSign derivativeSign hcoefficientSign hderivativeSign
    (fun i _ => hbounded i) (fun i _ => hextremal i)
    (fun i _ => hcoefficient i) (fun i _ => hcommon i)

end

end


-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-lagrange-unverified-v4.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-nodal-coefficient-unverified-v2.lean" SHA256 798a352b6d43b2550b87af47405b11e0955cbabea828124267e6448e4b6ee3e7

/- Uncompiled coefficient-positivity draft. No local-module imports or reports.
   The node derivative identity and positive scale are explicit inputs.
   In the intended positive-degree Chebyshev application, scale is n^2 at
   internal critical nodes and 2*n^2 at the endpoints. Degree zero is separate. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial

theorem MarkovNodalCoefficient.derivative_eval_scaled_nodal {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (omega : Polynomial Real) (lc : Real)
    (hp : omega = C lc * Lagrange.nodal nodes tau) (i : I) (hi : i ∈ nodes) :
    (derivative omega).eval (tau i) =
      lc * (nodes.erase i).prod (fun j => tau i - tau j) := by
  have h := congrArg (fun P : Polynomial Real => (derivative P).eval (tau i)) hp
  simpa only [derivative_C_mul, eval_mul, eval_C,
    Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal] using h

theorem MarkovNodalCoefficient.quotient_pos_of_scaled_unit (lc scale value denominator : Real)
    (hlc : 0 < lc) (hscale : 0 < scale) (hunit : |value| = 1)
    (hrelation : lc * denominator = scale * value) :
    denominator ≠ 0 ∧ value / denominator = lc / scale ∧ 0 < value / denominator := by
  have hvalue : value ≠ 0 := by
    intro hzero
    simp only [hzero, abs_zero, zero_ne_one] at hunit
  have hdenominator : denominator ≠ 0 := by
    intro hzero
    have hproduct : scale * value = 0 := by
      simpa only [hzero, mul_zero] using hrelation.symm
    exact hvalue ((mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hscale))
  have hquotient : value / denominator = lc / scale := by
    apply (div_eq_div_iff hdenominator (ne_of_gt hscale)).mpr
    calc
      value * scale = scale * value := mul_comm _ _
      _ = lc * denominator := hrelation.symm
  refine ⟨hdenominator, hquotient, ?_⟩
  rw [hquotient]
  exact div_pos hlc hscale

theorem MarkovNodalCoefficient.coefficient_pos_at_unit_node {I : Type*} [DecidableEq I]
    (nodes : Finset I) (tau : I -> Real) (omega Q : Polynomial Real) (lc scale : Real)
    (hp : omega = C lc * Lagrange.nodal nodes tau) (i : I) (hi : i ∈ nodes)
    (hlc : 0 < lc) (hscale : 0 < scale) (hunit : |Q.eval (tau i)| = 1)
    (hnode : (derivative omega).eval (tau i) = scale * Q.eval (tau i)) :
    (nodes.erase i).prod (fun j => tau i - tau j) ≠ 0 ∧
      Q.eval (tau i) / (nodes.erase i).prod (fun j => tau i - tau j) = lc / scale ∧
      0 < Q.eval (tau i) / (nodes.erase i).prod (fun j => tau i - tau j) := by
  have hrelation : lc * (nodes.erase i).prod (fun j => tau i - tau j) =
      scale * Q.eval (tau i) := by
    calc
      lc * (nodes.erase i).prod (fun j => tau i - tau j) =
          (derivative omega).eval (tau i) :=
        (derivative_eval_scaled_nodal nodes tau omega lc hp i hi).symm
      _ = scale * Q.eval (tau i) := hnode
  exact quotient_pos_of_scaled_unit lc scale (Q.eval (tau i))
    ((nodes.erase i).prod (fun j => tau i - tau j)) hlc hscale hunit hrelation

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-nodal-coefficient-unverified-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-nodal-degree-unverified-v1.lean" SHA256 395178918fcf43a2a18a11f3c6717622b703f64d6f873c1abe0d35f2c937c9b1

/- Uncompiled context-only degree and leading-coefficient facts for the
   Chebyshev nodal polynomial and its endpoint deletions. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial Polynomial.Chebyshev

def MarkovNodalDegree.omega (n : Nat) : Polynomial Real :=
  (X ^ 2 - 1) * (T Real (n : Int)).derivative

theorem MarkovNodalDegree.derivative_T_degree (n : Nat) (hn : 0 < n) :
    (T Real (n : Int)).derivative.degree = ((n - 1 : Nat) : WithBot Nat) := by
  have hdegree : (T Real (n : Int)).natDegree = n := by simp
  rw [degree_derivative_eq _ (by rw [hdegree]; exact hn), hdegree]

theorem MarkovNodalDegree.omega_degree (n : Nat) (hn : 0 < n) :
    (omega n).degree = ((n + 1 : Nat) : WithBot Nat) := by
  have hquadratic : (X ^ 2 - 1 : Polynomial Real).degree = (2 : WithBot Nat) := by
    simpa using degree_X_pow_sub_C (R := Real) (n := 2) (by decide) (1 : Real)
  rw [omega, degree_mul, hquadratic, derivative_T_degree n hn]
  exact_mod_cast (show 2 + (n - 1) = n + 1 by omega)

theorem MarkovNodalDegree.derivative_T_leadingCoeff (n : Nat) :
    (T Real (n : Int)).derivative.leadingCoeff = (2 : Real) ^ (n - 1) * (n : Real) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [T_derivative_eq_U]
    have h1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [h1, leadingCoeff_mul, leadingCoeff_U_natCast, ← C_eq_intCast, leadingCoeff_C]
    push_cast
    ring

theorem MarkovNodalDegree.omega_leadingCoeff (n : Nat) :
    (omega n).leadingCoeff = (2 : Real) ^ (n - 1) * (n : Real) := by
  simp [omega, leadingCoeff_X_pow_sub_one (show 0 < (2 : Nat) by decide),
    derivative_T_leadingCoeff]

theorem MarkovNodalDegree.omega_leadingCoeff_pos (n : Nat) (hn : 0 < n) :
    0 < (omega n).leadingCoeff := by
  rw [omega_leadingCoeff]
  exact mul_pos (pow_pos (by norm_num) _) (Nat.cast_pos.mpr hn)

theorem MarkovNodalDegree.linear_factor_T_derivative_degree (n : Nat) (hn : 0 < n) (t : Real) :
    ((X - C t) * (T Real (n : Int)).derivative).degree = (n : WithBot Nat) := by
  rw [degree_mul, degree_X_sub_C, derivative_T_degree n hn]
  exact_mod_cast (show 1 + (n - 1) = n by omega)

theorem MarkovNodalDegree.linear_factor_T_derivative_derivative_degree
    (n : Nat) (hn : 2 <= n) (t : Real) :
    (((X - C t) * (T Real (n : Int)).derivative).derivative).degree =
      ((n - 1 : Nat) : WithBot Nat) := by
  have hpositive : 0 < n := lt_of_lt_of_le (show 0 < (2 : Nat) by decide) hn
  have hdegree := linear_factor_T_derivative_degree n hpositive t
  have hnatDegree := natDegree_eq_of_degree_eq_some hdegree
  rw [degree_derivative_eq _ (by rw [hnatDegree]; exact hpositive), hnatDegree]

theorem MarkovNodalDegree.left_deleted_degree (n : Nat) (hn : 0 < n) :
    ((X - 1) * (T Real (n : Int)).derivative).degree = (n : WithBot Nat) := by
  simpa using linear_factor_T_derivative_degree n hn 1

theorem MarkovNodalDegree.right_deleted_degree (n : Nat) (hn : 0 < n) :
    ((X + 1) * (T Real (n : Int)).derivative).degree = (n : WithBot Nat) := by
  simpa using linear_factor_T_derivative_degree n hn (-1)

theorem MarkovNodalDegree.left_deleted_derivative_degree (n : Nat) (hn : 2 <= n) :
    (((X - 1) * (T Real (n : Int)).derivative).derivative).degree =
      ((n - 1 : Nat) : WithBot Nat) := by
  simpa using linear_factor_T_derivative_derivative_degree n hn 1

theorem MarkovNodalDegree.right_deleted_derivative_degree (n : Nat) (hn : 2 <= n) :
    (((X + 1) * (T Real (n : Int)).derivative).derivative).degree =
      ((n - 1 : Nat) : WithBot Nat) := by
  simpa using linear_factor_T_derivative_derivative_degree n hn (-1)

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-markov-nodal-degree-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-chebyshev-nodes-work-v2.lean" SHA256 158ff76ca2ce6636771a78c623c22d1b122309eef8661d18fa72a1a75f4acaa7

noncomputable section

section

open Polynomial Polynomial.Chebyshev Real Set

def ShadrinChebyshevNodes.chebyshev (n : ℕ) : ℝ[X] := T ℝ (n : ℤ)

def ShadrinChebyshevNodes.rootAngle (n k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * π / n

def ShadrinChebyshevNodes.criticalAngle (n k : ℕ) : ℝ := ((k : ℝ) + 1) * π / n

def ShadrinChebyshevNodes.rootNode (n k : ℕ) : ℝ := cos (π - rootAngle n k)

def ShadrinChebyshevNodes.criticalNode (n k : ℕ) : ℝ := cos (π - criticalAngle n k)

def ShadrinChebyshevNodes.orientation (n k : ℕ) : ℝ := -((-1 : ℝ) ^ n * (-1 : ℝ) ^ k)

def ShadrinChebyshevNodes.plusDeletedDerivative (n : ℕ) : ℝ[X] :=
  derivative ((X + 1) * derivative (chebyshev n))

def ShadrinChebyshevNodes.minusDeletedDerivative (n : ℕ) : ℝ[X] :=
  derivative ((X - 1) * derivative (chebyshev n))

private theorem ShadrinChebyshevNodes.orientation_mul_self (n k : ℕ) :
    orientation n k * orientation n k = 1 := by
  have hn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hk : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    orientation n k * orientation n k =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by
      unfold orientation
      ring
    _ = 1 := by rw [hn, hk, one_mul]

private theorem ShadrinChebyshevNodes.orientation_succ (n k : ℕ) :
    orientation n (k + 1) = -orientation n k := by
  unfold orientation
  rw [pow_succ]
  ring

private theorem ShadrinChebyshevNodes.root_angle_mem {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    0 < rootAngle n k ∧ rootAngle n k < π := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
  have hmul := mul_le_mul_of_nonneg_right hkR pi_pos.le
  constructor
  · exact div_pos (mul_pos (by positivity) pi_pos) hnR
  · unfold rootAngle
    apply (div_lt_iff₀ hnR).mpr
    nlinarith [pi_pos]

private theorem ShadrinChebyshevNodes.angle_chain {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n) :
    0 < rootAngle n k ∧
      rootAngle n k < criticalAngle n k ∧
      criticalAngle n k < rootAngle n (k + 1) ∧
      rootAngle n (k + 1) < π := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfirst := root_angle_mem hn (Nat.lt_of_succ_lt hk)
  have hlast := root_angle_mem hn hk
  refine ⟨hfirst.1, ?_, ?_, hlast.2⟩
  · unfold rootAngle criticalAngle
    apply (div_lt_div_iff_of_pos_right hnR).mpr
    nlinarith [pi_pos]
  · unfold rootAngle criticalAngle
    simp only [Nat.cast_add, Nat.cast_one]
    apply (div_lt_div_iff_of_pos_right hnR).mpr
    nlinarith [pi_pos]

theorem ShadrinChebyshevNodes.node_order {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n) :
    -1 < rootNode n k ∧ rootNode n k < criticalNode n k ∧
      criticalNode n k < rootNode n (k + 1) ∧ rootNode n (k + 1) < 1 := by
  rcases angle_chain hn hk with ⟨ha, hab, hbc, hc⟩
  have hb := ha.trans hab
  have hcp := hb.trans hbc
  have hbpi := hbc.trans hc
  have hapi := hab.trans hbpi
  have hleft := cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hapi.le ha
  have hright := cos_lt_cos_of_nonneg_of_le_pi hcp.le (le_refl π) hc
  have hmid1 := cos_lt_cos_of_nonneg_of_le_pi ha.le hbpi.le hab
  have hmid2 := cos_lt_cos_of_nonneg_of_le_pi hb.le hc.le hbc
  simp only [cos_zero, cos_pi] at hleft hright
  unfold rootNode criticalNode
  simp only [cos_pi_sub]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem ShadrinChebyshevNodes.root_phase (n k : ℕ) (hn : 0 < n) :
    (n : ℝ) * (π - rootAngle n k) =
      (n : ℝ) * π - ((k : ℝ) * π + π / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold rootAngle
  field_simp [hn0]

private theorem ShadrinChebyshevNodes.critical_phase (n k : ℕ) (hn : 0 < n) :
    (n : ℝ) * (π - criticalAngle n k) =
      (n : ℝ) * π - ((k + 1 : ℕ) : ℝ) * π := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold criticalAngle
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hn0]

theorem ShadrinChebyshevNodes.root_eval (n k : ℕ) (hn : 0 < n) :
    (chebyshev n).eval (rootNode n k) = 0 := by
  rw [rootNode, chebyshev, T_real_cos]
  simp only [Int.cast_natCast]
  rw [root_phase n k hn, cos_nat_mul_pi_sub, cos_add_pi_div_two, sin_nat_mul_pi]
  ring

theorem ShadrinChebyshevNodes.critical_eval (n k : ℕ) (hn : 0 < n) :
    (chebyshev n).eval (criticalNode n k) = orientation n k := by
  rw [criticalNode, chebyshev, T_real_cos]
  simp only [Int.cast_natCast]
  rw [critical_phase n k hn, cos_nat_mul_pi_sub, cos_nat_mul_pi, pow_succ]
  unfold orientation
  ring

private theorem ShadrinChebyshevNodes.derivative_cos_identity (n : ℕ) (theta : ℝ) :
    (chebyshev n).derivative.eval (cos theta) * sin theta =
      (n : ℝ) * sin ((n : ℝ) * theta) := by
  simp [chebyshev, T_derivative_eq_U, mul_assoc]

private theorem ShadrinChebyshevNodes.root_derivative_sine (n k : ℕ) (hn : 0 < n) :
    (chebyshev n).derivative.eval (rootNode n k) * sin (π - rootAngle n k) =
      (n : ℝ) * orientation n k := by
  have h := derivative_cos_identity n (π - rootAngle n k)
  rw [root_phase n k hn, sin_nat_mul_pi_sub, sin_add_pi_div_two, cos_nat_mul_pi] at h
  simpa only [rootNode, orientation] using h

theorem ShadrinChebyshevNodes.critical_derivative {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n) :
    (chebyshev n).derivative.eval (criticalNode n k) = 0 := by
  rcases angle_chain hn hk with ⟨ha, hab, hbc, hc⟩
  have hsin : 0 < sin (π - criticalAngle n k) :=
    sin_pos_of_pos_of_lt_pi (sub_pos.mpr (hbc.trans hc)) (by linarith [ha.trans hab])
  have h := derivative_cos_identity n (π - criticalAngle n k)
  rw [critical_phase n k hn, sin_nat_mul_pi_sub, sin_nat_mul_pi] at h
  simp only [mul_zero, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hsin.ne'

theorem ShadrinChebyshevNodes.root_derivative_oriented_pos {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    0 < orientation n k * (chebyshev n).derivative.eval (rootNode n k) := by
  have hangles := root_angle_mem hn hk
  have hsin : 0 < sin (π - rootAngle n k) :=
    sin_pos_of_pos_of_lt_pi (sub_pos.mpr hangles.2) (by linarith [hangles.1])
  have hmul :
      (orientation n k * (chebyshev n).derivative.eval (rootNode n k)) *
        sin (π - rootAngle n k) = (n : ℝ) := by
    calc
      _ = orientation n k *
          ((chebyshev n).derivative.eval (rootNode n k) * sin (π - rootAngle n k)) := by
        ring
      _ = orientation n k * ((n : ℝ) * orientation n k) := by
        rw [root_derivative_sine n k hn]
      _ = (n : ℝ) * (orientation n k * orientation n k) := by ring
      _ = n := by rw [orientation_mul_self, mul_one]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact pos_of_mul_pos_left (hmul.symm ▸ hnR) hsin.le

theorem ShadrinChebyshevNodes.chebyshev_ode_eval (n : ℕ) (x : ℝ) :
    (x ^ 2 - 1) * (chebyshev n).derivative.derivative.eval x +
      x * (chebyshev n).derivative.eval x = (n : ℝ) ^ 2 * (chebyshev n).eval x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) (n : ℤ))
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    eval_mul, eval_sub, eval_one, eval_pow, eval_X, Int.cast_natCast, eval_natCast] at h
  change (1 - x ^ 2) * (chebyshev n).derivative.derivative.eval x =
    x * (chebyshev n).derivative.eval x - (n : ℝ) ^ 2 * (chebyshev n).eval x at h
  nlinarith only [h]

theorem ShadrinChebyshevNodes.plus_deleted_eval (n : ℕ) (x : ℝ) :
    (1 - x) * (plusDeletedDerivative n).eval x =
      (chebyshev n).derivative.eval x - (n : ℝ) ^ 2 * (chebyshev n).eval x := by
  have h := chebyshev_ode_eval n x
  simp only [plusDeletedDerivative, derivative_mul, derivative_add, derivative_X,
    derivative_one, add_zero, one_mul, eval_add, eval_mul, eval_X, eval_one]
  nlinarith only [h]

theorem ShadrinChebyshevNodes.minus_deleted_eval (n : ℕ) (x : ℝ) :
    (1 + x) * (minusDeletedDerivative n).eval x =
      (chebyshev n).derivative.eval x + (n : ℝ) ^ 2 * (chebyshev n).eval x := by
  have h := chebyshev_ode_eval n x
  simp only [minusDeletedDerivative, derivative_mul, derivative_sub, derivative_X,
    derivative_one, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_one]
  nlinarith only [h]

theorem ShadrinChebyshevNodes.exists_endpoint_deleted_derivative_roots {n k : ℕ}
    (hn : 2 ≤ n) (hk : k + 1 < n) :
    (∃ xi ∈ Ioo (rootNode n k) (criticalNode n k),
      (plusDeletedDerivative n).eval xi = 0) ∧
    (∃ eta ∈ Ioo (criticalNode n k) (rootNode n (k + 1)),
      (minusDeletedDerivative n).eval eta = 0) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnR 2
  rcases node_order hnpos hk with ⟨hzlo, hzcrit, hcritnext, hzhi⟩
  have hcritlo : -1 < criticalNode n k := hzlo.trans hzcrit
  have hcrithi : criticalNode n k < 1 := hcritnext.trans hzhi
  have hzfirsthi : rootNode n k < 1 := hzcrit.trans hcrithi
  have hznextlo : -1 < rootNode n (k + 1) := hcritlo.trans hcritnext
  let e : ℝ := orientation n k
  have he : e ≠ 0 := by
    have hsquare : e * e = 1 := orientation_mul_self n k
    intro hzero
    rw [hzero, zero_mul] at hsquare
    norm_num at hsquare
  have hcritvalue : e * (chebyshev n).eval (criticalNode n k) = 1 := by
    rw [critical_eval n k hnpos]
    exact orientation_mul_self n k
  have hcritderiv := critical_derivative hnpos hk
  have hfirstderiv : 0 < e * (chebyshev n).derivative.eval (rootNode n k) :=
    root_derivative_oriented_pos hnpos (Nat.lt_of_succ_lt hk)
  have hnextderiv : e * (chebyshev n).derivative.eval (rootNode n (k + 1)) < 0 := by
    have h := root_derivative_oriented_pos hnpos hk
    rw [orientation_succ] at h
    dsimp [e]
    nlinarith only [h]
  have hplus (y : ℝ) :
      (1 - y) * (e * (plusDeletedDerivative n).eval y) =
        e * (chebyshev n).derivative.eval y - (n : ℝ) ^ 2 * (e * (chebyshev n).eval y) := by
    calc
      _ = e * ((1 - y) * (plusDeletedDerivative n).eval y) := by ring
      _ = e * ((chebyshev n).derivative.eval y - (n : ℝ) ^ 2 * (chebyshev n).eval y) := by
        rw [plus_deleted_eval]
      _ = _ := by ring
  have hminus (y : ℝ) :
      (1 + y) * (e * (minusDeletedDerivative n).eval y) =
        e * (chebyshev n).derivative.eval y + (n : ℝ) ^ 2 * (e * (chebyshev n).eval y) := by
    calc
      _ = e * ((1 + y) * (minusDeletedDerivative n).eval y) := by ring
      _ = e * ((chebyshev n).derivative.eval y + (n : ℝ) ^ 2 * (chebyshev n).eval y) := by
        rw [minus_deleted_eval]
      _ = _ := by ring
  have hplusleft : 0 < e * (plusDeletedDerivative n).eval (rootNode n k) := by
    apply pos_of_mul_pos_right (a := 1 - rootNode n k) ?_ (sub_nonneg.mpr hzfirsthi.le)
    rw [hplus, root_eval n k hnpos, mul_zero, mul_zero, sub_zero]
    exact hfirstderiv
  have hplusright : e * (plusDeletedDerivative n).eval (criticalNode n k) < 0 := by
    apply neg_of_mul_neg_right (a := 1 - criticalNode n k) ?_ (sub_nonneg.mpr hcrithi.le)
    rw [hplus, hcritderiv, mul_zero, hcritvalue, mul_one, zero_sub]
    exact neg_neg_of_pos hn2
  have hminusleft : 0 < e * (minusDeletedDerivative n).eval (criticalNode n k) := by
    apply pos_of_mul_pos_right (a := 1 + criticalNode n k) ?_ (by linarith)
    rw [hminus, hcritderiv, mul_zero, hcritvalue, mul_one, zero_add]
    exact hn2
  have hminusright : e * (minusDeletedDerivative n).eval (rootNode n (k + 1)) < 0 := by
    apply neg_of_mul_neg_right (a := 1 + rootNode n (k + 1)) ?_ (by linarith)
    rw [hminus, root_eval n (k + 1) hnpos, mul_zero, mul_zero, add_zero]
    exact hnextderiv
  have hpluscont : Continuous (fun y => e * (plusDeletedDerivative n).eval y) :=
    continuous_const.mul (plusDeletedDerivative n).continuous
  have hminuscont : Continuous (fun y => e * (minusDeletedDerivative n).eval y) :=
    continuous_const.mul (minusDeletedDerivative n).continuous
  obtain ⟨xi, hxi, hxiRoot⟩ := intermediate_value_Ioo' hzcrit.le
    hpluscont.continuousOn ⟨hplusright, hplusleft⟩
  obtain ⟨eta, heta, hetaRoot⟩ := intermediate_value_Ioo' hcritnext.le
    hminuscont.continuousOn ⟨hminusright, hminusleft⟩
  exact ⟨⟨xi, hxi, (mul_eq_zero.mp hxiRoot).resolve_left he⟩,
    ⟨eta, heta, (mul_eq_zero.mp hetaRoot).resolve_left he⟩⟩

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-chebyshev-nodes-work-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-node-geometry-work-v2.lean" SHA256 3c986ef8cdfa11c045baba89aa76207ca3a2fb624a4489e06c535a67fb2bd76a
-- Append after the checked ShadrinChebyshevNodes source; this body uses only its public declarations.
section

open Polynomial Real Set

theorem ShadrinChebyshevNodes.rootAngle_mem_Ioo {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    rootAngle n k ∈ Ioo 0 π := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
  have hmul := mul_le_mul_of_nonneg_right hkR pi_pos.le
  constructor
  · exact div_pos (mul_pos (by positivity) pi_pos) hnR
  · unfold rootAngle
    apply (div_lt_iff₀ hnR).mpr
    nlinarith [pi_pos]

theorem ShadrinChebyshevNodes.rootNode_mem_Ioo {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    rootNode n k ∈ Ioo (-1) 1 := by
  have ha := rootAngle_mem_Ioo hn hk
  have hleft := cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) ha.2.le ha.1
  have hright := cos_lt_cos_of_nonneg_of_le_pi ha.1.le (le_refl π) ha.2
  simp only [cos_zero, cos_pi] at hleft hright
  unfold rootNode
  simp only [cos_pi_sub]
  exact ⟨by linarith, by linarith⟩

theorem ShadrinChebyshevNodes.rootNode_lt {n k l : ℕ} (hkl : k < l) (hl : l < n) :
    rootNode n k < rootNode n l := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le l) hl
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hklR : (k : ℝ) < l := by exact_mod_cast hkl
  have hak := rootAngle_mem_Ioo hn (hkl.trans hl)
  have hal := rootAngle_mem_Ioo hn hl
  have hangle : rootAngle n k < rootAngle n l := by
    unfold rootAngle
    apply (div_lt_div_iff_of_pos_right hnR).mpr
    exact mul_lt_mul_of_pos_right (by linarith only [hklR]) pi_pos
  have hcos := cos_lt_cos_of_nonneg_of_le_pi hak.1.le hal.2.le hangle
  unfold rootNode
  simp only [cos_pi_sub]
  exact neg_lt_neg hcos

theorem ShadrinChebyshevNodes.rootNode_le {n k l : ℕ} (hkl : k ≤ l) (hl : l < n) :
    rootNode n k ≤ rootNode n l := by
  rcases eq_or_lt_of_le hkl with heq | hlt
  · rw [heq]
  · exact (rootNode_lt hlt hl).le

theorem ShadrinChebyshevNodes.rootNode_strictMono (n : ℕ) :
    StrictMono (fun i : Fin n => rootNode n i.val) := by
  intro i j hij
  exact rootNode_lt hij j.isLt

theorem ShadrinChebyshevNodes.abs_orientation (n k : ℕ) : |orientation n k| = 1 := by
  simp [orientation, abs_mul, abs_pow]

theorem ShadrinChebyshevNodes.abs_critical_eval (n k : ℕ) (hn : 0 < n) :
    |(chebyshev n).eval (criticalNode n k)| = 1 := by
  rw [critical_eval n k hn, abs_orientation]

theorem ShadrinChebyshevNodes.criticalNode_mem_Ioo {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n) :
    criticalNode n k ∈ Ioo (-1) 1 := by
  rcases node_order hn hk with ⟨hzlo, hzcrit, hcritnext, hzhi⟩
  exact ⟨hzlo.trans hzcrit, hcritnext.trans hzhi⟩

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-node-geometry-work-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-root-arrays-unverified-v1.lean" SHA256 ab1d74c419714c0abb12323fe491efa1a6d597854552fec9e058f46c5460b62a
-- Append after ShadrinChebyshevNodes, its geometry body, MarkovNodalDegree, and MarkovSignIntervals.
noncomputable section

section

open Polynomial Set ShadrinChebyshevNodes

private theorem ShadrinRootArrays.index_bound {n : ℕ} (i : Fin (n - 1)) : i.val + 1 < n := by
  have hi := i.isLt
  omega

def ShadrinRootArrays.xi (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) : ℝ :=
  Classical.choose ((exists_endpoint_deleted_derivative_roots hn (index_bound i)).1)

def ShadrinRootArrays.eta (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) : ℝ :=
  Classical.choose ((exists_endpoint_deleted_derivative_roots hn (index_bound i)).2)

private theorem ShadrinRootArrays.xi_spec (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    xi n hn i ∈ Ioo (rootNode n i.val) (criticalNode n i.val) ∧
      (plusDeletedDerivative n).eval (xi n hn i) = 0 :=
  Classical.choose_spec ((exists_endpoint_deleted_derivative_roots hn (index_bound i)).1)

private theorem ShadrinRootArrays.eta_spec (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    eta n hn i ∈ Ioo (criticalNode n i.val) (rootNode n (i.val + 1)) ∧
      (minusDeletedDerivative n).eval (eta n hn i) = 0 :=
  Classical.choose_spec ((exists_endpoint_deleted_derivative_roots hn (index_bound i)).2)

theorem ShadrinRootArrays.chain (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    rootNode n i.val < xi n hn i ∧
      xi n hn i < criticalNode n i.val ∧
      criticalNode n i.val < eta n hn i ∧
      eta n hn i < rootNode n (i.val + 1) :=
  ⟨(xi_spec n hn i).1.1, (xi_spec n hn i).1.2,
    (eta_spec n hn i).1.1, (eta_spec n hn i).1.2⟩

theorem ShadrinRootArrays.xi_root (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    (plusDeletedDerivative n).eval (xi n hn i) = 0 :=
  (xi_spec n hn i).2

theorem ShadrinRootArrays.eta_root (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    (minusDeletedDerivative n).eval (eta n hn i) = 0 :=
  (eta_spec n hn i).2

theorem ShadrinRootArrays.xi_strictMono (n : ℕ) (hn : 2 ≤ n) : StrictMono (xi n hn) := by
  intro i j hij
  have hi := chain n hn i
  have hj := chain n hn j
  have hjn : j.val < n := lt_of_lt_of_le j.isLt (Nat.sub_le n 1)
  calc
    xi n hn i < criticalNode n i.val := hi.2.1
    _ < eta n hn i := hi.2.2.1
    _ < rootNode n (i.val + 1) := hi.2.2.2
    _ ≤ rootNode n j.val := rootNode_le (Nat.succ_le_of_lt hij) hjn
    _ < xi n hn j := hj.1

theorem ShadrinRootArrays.eta_strictMono (n : ℕ) (hn : 2 ≤ n) : StrictMono (eta n hn) := by
  intro i j hij
  have hi := chain n hn i
  have hj := chain n hn j
  have hjn : j.val < n := lt_of_lt_of_le j.isLt (Nat.sub_le n 1)
  calc
    eta n hn i < rootNode n (i.val + 1) := hi.2.2.2
    _ ≤ rootNode n j.val := rootNode_le (Nat.succ_le_of_lt hij) hjn
    _ < xi n hn j := hj.1
    _ < criticalNode n j.val := hj.2.1
    _ < eta n hn j := hj.2.2.1

theorem ShadrinRootArrays.xi_mem_Ioo (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    xi n hn i ∈ Ioo (-1) 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hin : i.val < n := lt_of_lt_of_le i.isLt (Nat.sub_le n 1)
  have hz := rootNode_mem_Ioo hnpos hin
  have ht := criticalNode_mem_Ioo hnpos (index_bound i)
  have hi := chain n hn i
  exact ⟨hz.1.trans hi.1, hi.2.1.trans ht.2⟩

theorem ShadrinRootArrays.eta_mem_Ioo (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    eta n hn i ∈ Ioo (-1) 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have ht := criticalNode_mem_Ioo hnpos (index_bound i)
  have hz := rootNode_mem_Ioo hnpos (index_bound i)
  have hi := chain n hn i
  exact ⟨ht.1.trans hi.2.2.1, hi.2.2.2.trans hz.2⟩

theorem ShadrinRootArrays.xi_degree (n : ℕ) (hn : 2 ≤ n) :
    (plusDeletedDerivative n).degree = ((n - 1 : ℕ) : WithBot ℕ) :=
  MarkovNodalDegree.right_deleted_derivative_degree n hn

theorem ShadrinRootArrays.eta_degree (n : ℕ) (hn : 2 ≤ n) :
    (minusDeletedDerivative n).degree = ((n - 1 : ℕ) : WithBot ℕ) :=
  MarkovNodalDegree.left_deleted_derivative_degree n hn

theorem ShadrinRootArrays.xi_exhaustive (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : (plusDeletedDerivative n).eval x = 0) : ∃ i, x = xi n hn i :=
  MarkovSignIntervals.roots_exhausted (n := n - 1)
    (plusDeletedDerivative n) (xi n hn) (xi_degree n hn)
    (xi_strictMono n hn).injective (xi_root n hn) x hx

theorem ShadrinRootArrays.eta_exhaustive (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : (minusDeletedDerivative n).eval x = 0) : ∃ i, x = eta n hn i :=
  MarkovSignIntervals.roots_exhausted (n := n - 1)
    (minusDeletedDerivative n) (eta n hn) (eta_degree n hn)
    (eta_strictMono n hn).injective (eta_root n hn) x hx

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-root-arrays-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-critical-roots-unverified-v1.lean" SHA256 718dff9d76fb78edb238df0d2590ab52121e1ec4ca6d3f0edf6cde6daa83369f
-- Append after nodes, node geometry, MarkovNodalDegree, and MarkovSignIntervals.
noncomputable section

section

open Polynomial Set ShadrinChebyshevNodes

def ShadrinCriticalRoots.nodes (n : ℕ) (i : Fin (n - 1)) : ℝ := criticalNode n i.val

private theorem ShadrinCriticalRoots.index_bound {n : ℕ} (i : Fin (n - 1)) : i.val + 1 < n := by
  have hi := i.isLt
  omega

theorem ShadrinCriticalRoots.strictMono (n : ℕ) (hn : 2 ≤ n) : StrictMono (nodes n) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  intro i j hij
  have hi := node_order hnpos (index_bound i)
  have hj := node_order hnpos (index_bound j)
  have hjn : j.val < n := lt_of_lt_of_le j.isLt (Nat.sub_le n 1)
  calc
    nodes n i < rootNode n (i.val + 1) := hi.2.2.1
    _ ≤ rootNode n j.val := rootNode_le (Nat.succ_le_of_lt hij) hjn
    _ < nodes n j := hj.2.1

theorem ShadrinCriticalRoots.root (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    (chebyshev n).derivative.eval (nodes n i) = 0 :=
  critical_derivative (lt_of_lt_of_le (by decide : 0 < 2) hn) (index_bound i)

theorem ShadrinCriticalRoots.degree (n : ℕ) (hn : 2 ≤ n) :
    (chebyshev n).derivative.degree = ((n - 1 : ℕ) : WithBot ℕ) :=
  MarkovNodalDegree.derivative_T_degree n (lt_of_lt_of_le (by decide : 0 < 2) hn)

theorem ShadrinCriticalRoots.exhaustive (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : (chebyshev n).derivative.eval x = 0) : ∃ i, x = nodes n i :=
  MarkovSignIntervals.roots_exhausted (n := n - 1)
    (chebyshev n).derivative (nodes n) (degree n hn)
    (strictMono n hn).injective (root n hn) x hx

theorem ShadrinCriticalRoots.mem_Ioo (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    nodes n i ∈ Ioo (-1) 1 :=
  criticalNode_mem_Ioo (lt_of_lt_of_le (by decide : 0 < 2) hn) (index_bound i)

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-critical-roots-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-comparison-intervals-v1.lean" SHA256 fa3249040f404af960ecfd793e54c301054bb5bd0d19d3b660ecc6e697176d5f
-- Combine after the checked node geometry and root-array declarations.
section

open Set ShadrinChebyshevNodes ShadrinRootArrays

noncomputable def ShadrinComparisonIntervals.left (n : Nat) (hn : 2 ≤ n) (i : Fin n) : Real :=
  if hi : i.val = 0 then -1 else eta n hn ⟨i.val - 1, by omega⟩

noncomputable def ShadrinComparisonIntervals.right (n : Nat) (hn : 2 ≤ n) (i : Fin n) : Real :=
  if hi : i.val + 1 < n then xi n hn ⟨i.val, by omega⟩ else 1

theorem ShadrinComparisonIntervals.root_inside (n : Nat) (hn : 2 ≤ n) (i : Fin n) :
    rootNode n i.val ∈ Ioo (left n hn i) (right n hn i) := by
  have hnpos : 0 < n := by omega
  have hz := rootNode_mem_Ioo hnpos i.isLt
  constructor
  · unfold left
    split_ifs with hi
    · exact hz.1
    · have h := (chain n hn ⟨i.val - 1, by omega⟩).2.2.2
      simpa only [Nat.sub_add_cancel (show 1 ≤ i.val by omega)] using h
  · unfold right
    split_ifs with hi
    · exact (chain n hn ⟨i.val, by omega⟩).1
    · exact hz.2

theorem ShadrinComparisonIntervals.interval_nonempty (n : Nat) (hn : 2 ≤ n) (i : Fin n) :
    left n hn i < right n hn i := (root_inside n hn i).1.trans (root_inside n hn i).2

theorem ShadrinComparisonIntervals.interval_bounds (n : Nat) (hn : 2 ≤ n) (i : Fin n) :
    -1 ≤ left n hn i ∧ right n hn i ≤ 1 := by
  have hnpos : 0 < n := by omega
  constructor
  · unfold left
    split_ifs with hi
    · exact le_rfl
    · have h := chain n hn ⟨i.val - 1, by omega⟩
      exact ((rootNode_mem_Ioo hnpos (show i.val - 1 < n by omega)).1.trans
        (h.1.trans (h.2.1.trans h.2.2.1))).le
  · unfold right
    split_ifs with hi
    · have h := chain n hn ⟨i.val, by omega⟩
      exact ((h.2.1.trans (h.2.2.1.trans h.2.2.2)).trans
        (rootNode_mem_Ioo hnpos hi).2).le
    · exact le_rfl

theorem ShadrinComparisonIntervals.ordered (n : Nat) (hn : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    right n hn i < left n hn j := by
  have hi : i.val + 1 < n := by omega
  have hj : j.val ≠ 0 := by omega
  rw [right, dif_pos hi, left, dif_neg hj]
  let a : Fin (n - 1) := ⟨i.val, by omega⟩
  let b : Fin (n - 1) := ⟨j.val - 1, by omega⟩
  have hab : a ≤ b := by change i.val ≤ j.val - 1; omega
  exact ((chain n hn a).2.1.trans (chain n hn a).2.2.1).trans_le
    ((eta_strictMono n hn).monotone hab)

theorem ShadrinComparisonIntervals.xi_not_mem (n : Nat) (hn : 2 ≤ n) (i : Fin n) (k : Fin (n - 1)) :
    xi n hn k ∉ Ioo (left n hn i) (right n hn i) := by
  intro hx
  by_cases hki : k.val < i.val
  · have hi : i.val ≠ 0 := by omega
    rw [left, dif_neg hi] at hx
    let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hkj : k ≤ j := by change k.val ≤ i.val - 1; omega
    have hbound : xi n hn k < eta n hn j :=
      ((chain n hn k).2.1.trans (chain n hn k).2.2.1).trans_le
        ((eta_strictMono n hn).monotone hkj)
    exact (not_lt_of_ge hbound.le) hx.1
  · have hi : i.val + 1 < n := by omega
    rw [right, dif_pos hi] at hx
    let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have hjk : j ≤ k := by change i.val ≤ k.val; omega
    exact (not_lt_of_ge ((xi_strictMono n hn).monotone hjk)) hx.2

theorem ShadrinComparisonIntervals.eta_not_mem (n : Nat) (hn : 2 ≤ n) (i : Fin n) (k : Fin (n - 1)) :
    eta n hn k ∉ Ioo (left n hn i) (right n hn i) := by
  intro hx
  by_cases hki : k.val < i.val
  · have hi : i.val ≠ 0 := by omega
    rw [left, dif_neg hi] at hx
    let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hkj : k ≤ j := by change k.val ≤ i.val - 1; omega
    exact (not_lt_of_ge ((eta_strictMono n hn).monotone hkj)) hx.1
  · have hi : i.val + 1 < n := by omega
    rw [right, dif_pos hi] at hx
    let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have hjk : j ≤ k := by change i.val ≤ k.val; omega
    have hbound : xi n hn j < eta n hn k :=
      ((chain n hn j).2.1.trans (chain n hn j).2.2.1).trans_le
        ((eta_strictMono n hn).monotone hjk)
    exact (not_lt_of_ge hbound.le) hx.2

theorem ShadrinComparisonIntervals.critical_not_mem (n : Nat) (hn : 2 ≤ n) (i : Fin n) (k : Fin (n - 1)) :
    criticalNode n k.val ∉ Icc (left n hn i) (right n hn i) := by
  intro hx
  by_cases hki : k.val < i.val
  · have hi : i.val ≠ 0 := by omega
    rw [left, dif_neg hi] at hx
    let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hkj : k ≤ j := by change k.val ≤ i.val - 1; omega
    have hbound : criticalNode n k.val < eta n hn j :=
      (chain n hn k).2.2.1.trans_le ((eta_strictMono n hn).monotone hkj)
    exact (not_le_of_gt hbound) hx.1
  · have hi : i.val + 1 < n := by omega
    rw [right, dif_pos hi] at hx
    let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have hjk : j ≤ k := by change i.val ≤ k.val; omega
    have hbound : xi n hn j < criticalNode n k.val :=
      ((xi_strictMono n hn).monotone hjk).trans_lt (chain n hn k).2.1
    exact (not_le_of_gt hbound) hx.2

theorem ShadrinComparisonIntervals.plus_nonzero (n : Nat) (hn : 2 ≤ n) (i : Fin n)
    {x : Real} (hx : x ∈ Ioo (left n hn i) (right n hn i)) :
    (plusDeletedDerivative n).eval x ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := xi_exhaustive n hn x hzero
  exact xi_not_mem n hn i k (hk ▸ hx)

theorem ShadrinComparisonIntervals.minus_nonzero (n : Nat) (hn : 2 ≤ n) (i : Fin n)
    {x : Real} (hx : x ∈ Ioo (left n hn i) (right n hn i)) :
    (minusDeletedDerivative n).eval x ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := eta_exhaustive n hn x hzero
  exact eta_not_mem n hn i k (hk ▸ hx)

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-comparison-intervals-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-comparison-signs-work-v2.lean" SHA256 cd50e16ca73b069acefe9e525df4c1a4c8fcd3b193dd5dfe588b5ab86aa7de7d
-- Append after comparison intervals, critical roots, and their checked prerequisites.
section

open Polynomial Set ShadrinChebyshevNodes ShadrinRootArrays ShadrinComparisonIntervals

private theorem ShadrinComparisonSigns.orientation_nonzero (n k : ℕ) : orientation n k ≠ 0 := by
  intro hzero
  have h := abs_orientation n k
  simp [hzero] at h

theorem ShadrinComparisonSigns.derivative_nonzero (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc (left n hn i) (right n hn i)) :
    (chebyshev n).derivative.eval x ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := ShadrinCriticalRoots.exhaustive n hn x hzero
  have hmem : ShadrinCriticalRoots.nodes n k ∈ Icc (left n hn i) (right n hn i) :=
    hk ▸ hx
  exact critical_not_mem n hn i k hmem

theorem ShadrinComparisonSigns.derivative_oriented_pos (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc (left n hn i) (right n hn i)) :
    0 < orientation n i.val * (chebyshev n).derivative.eval x := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnonneg := MarkovSignIntervals.signed_nonneg_on_closed
    (chebyshev n).derivative (orientation n i.val) (root_inside n hn i)
    (root_derivative_oriented_pos hnpos i.isLt)
    (fun y hy => derivative_nonzero n hn i ⟨hy.1.le, hy.2.le⟩) x hx
  exact lt_of_le_of_ne hnonneg
    (mul_ne_zero (orientation_nonzero n i.val) (derivative_nonzero n hn i hx)).symm

theorem ShadrinComparisonSigns.plus_nonneg (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc (left n hn i) (right n hn i)) :
    0 ≤ orientation n i.val * (plusDeletedDerivative n).eval x := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hz := rootNode_mem_Ioo hnpos i.isLt
  have hderiv := root_derivative_oriented_pos hnpos i.isLt
  have heq :
      (1 - rootNode n i.val) *
        (orientation n i.val * (plusDeletedDerivative n).eval (rootNode n i.val)) =
      orientation n i.val * (chebyshev n).derivative.eval (rootNode n i.val) := by
    calc
      _ = orientation n i.val *
          ((1 - rootNode n i.val) * (plusDeletedDerivative n).eval (rootNode n i.val)) := by
        ring
      _ = _ := by
        rw [plus_deleted_eval, root_eval n i.val hnpos, mul_zero, sub_zero]
  have hpositive : 0 < orientation n i.val *
      (plusDeletedDerivative n).eval (rootNode n i.val) :=
    pos_of_mul_pos_right (heq.symm ▸ hderiv) (sub_nonneg.mpr hz.2.le)
  exact MarkovSignIntervals.signed_nonneg_on_closed
    (plusDeletedDerivative n) (orientation n i.val) (root_inside n hn i) hpositive
    (fun y hy => ShadrinComparisonIntervals.plus_nonzero n hn i hy) x hx

theorem ShadrinComparisonSigns.minus_nonneg (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc (left n hn i) (right n hn i)) :
    0 ≤ orientation n i.val * (minusDeletedDerivative n).eval x := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hz := rootNode_mem_Ioo hnpos i.isLt
  have hderiv := root_derivative_oriented_pos hnpos i.isLt
  have heq :
      (1 + rootNode n i.val) *
        (orientation n i.val * (minusDeletedDerivative n).eval (rootNode n i.val)) =
      orientation n i.val * (chebyshev n).derivative.eval (rootNode n i.val) := by
    calc
      _ = orientation n i.val *
          ((1 + rootNode n i.val) * (minusDeletedDerivative n).eval (rootNode n i.val)) := by
        ring
      _ = _ := by
        rw [minus_deleted_eval, root_eval n i.val hnpos, mul_zero, add_zero]
  have hpositive : 0 < orientation n i.val *
      (minusDeletedDerivative n).eval (rootNode n i.val) :=
    pos_of_mul_pos_right (heq.symm ▸ hderiv) (by linarith only [hz.1])
  exact MarkovSignIntervals.signed_nonneg_on_closed
    (minusDeletedDerivative n) (orientation n i.val) (root_inside n hn i) hpositive
    (fun y hy => ShadrinComparisonIntervals.minus_nonzero n hn i hy) x hx

theorem ShadrinComparisonSigns.left_identity (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (n : ℝ) ^ 2 * (chebyshev n).eval (left n hn i) =
      -(chebyshev n).derivative.eval (left n hn i) := by
  unfold left
  split_ifs with hi
  · have h := minus_deleted_eval n (-1)
    nlinarith only [h]
  · let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have h := minus_deleted_eval n (eta n hn j)
    rw [eta_root n hn j, mul_zero] at h
    change (n : ℝ) ^ 2 * (chebyshev n).eval (eta n hn j) =
      -(chebyshev n).derivative.eval (eta n hn j)
    nlinarith only [h]

theorem ShadrinComparisonSigns.right_identity (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (n : ℝ) ^ 2 * (chebyshev n).eval (right n hn i) =
      (chebyshev n).derivative.eval (right n hn i) := by
  unfold right
  split_ifs with hi
  · let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have h := plus_deleted_eval n (xi n hn j)
    rw [xi_root n hn j, mul_zero] at h
    change (n : ℝ) ^ 2 * (chebyshev n).eval (xi n hn j) =
      (chebyshev n).derivative.eval (xi n hn j)
    nlinarith only [h]
  · have h := plus_deleted_eval n 1
    nlinarith only [h]

theorem ShadrinComparisonSigns.oriented_endpoint_signs (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    orientation n i.val * ((n : ℝ) ^ 2 * (chebyshev n).eval (left n hn i)) < 0 ∧
      0 < orientation n i.val * ((n : ℝ) ^ 2 * (chebyshev n).eval (right n hn i)) := by
  have hab := (interval_nonempty n hn i).le
  have hleft := derivative_oriented_pos n hn i (show left n hn i ∈
    Icc (left n hn i) (right n hn i) from ⟨le_rfl, hab⟩)
  have hright := derivative_oriented_pos n hn i (show right n hn i ∈
    Icc (left n hn i) (right n hn i) from ⟨hab, le_rfl⟩)
  constructor
  · rw [left_identity]
    nlinarith only [hleft]
  · rw [right_identity]
    exact hright

theorem ShadrinComparisonSigns.endpoint_signs (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    ((n : ℝ) ^ 2 * (chebyshev n).eval (left n hn i) < 0 ∧
      0 < (n : ℝ) ^ 2 * (chebyshev n).eval (right n hn i)) ∨
    (0 < (n : ℝ) ^ 2 * (chebyshev n).eval (left n hn i) ∧
      (n : ℝ) ^ 2 * (chebyshev n).eval (right n hn i) < 0) := by
  rcases oriented_endpoint_signs n hn i with ⟨hleft, hright⟩
  rcases lt_or_gt_of_ne (orientation_nonzero n i.val) with hnegative | hpositive
  · right
    constructor
    · have hflip : 0 < (-orientation n i.val) *
          ((n : ℝ) ^ 2 * (chebyshev n).eval (left n hn i)) := by
        nlinarith only [hleft]
      exact pos_of_mul_pos_right hflip (neg_nonneg.mpr hnegative.le)
    · exact neg_of_mul_pos_right hright hnegative.le
  · left
    exact ⟨neg_of_mul_neg_right hleft hpositive.le, pos_of_mul_pos_right hright hpositive.le⟩

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-markov-comparison-signs-work-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-interpolation-nodes-unverified-v2.lean" SHA256 a270fc2bf13104129b6ece716c5ee1b8937f81b4976cc15675e25b37650ee093
/- Uncompiled body. Append after ShadrinChebyshevNodes, its geometry body,
   and MarkovNodalDegree. Root owns assembly and verification. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial Polynomial.Chebyshev ShadrinChebyshevNodes

def MarkovInterpolationNodes.tau (n : Nat) (i : Fin (n + 1)) : Real :=
  if i.val = 0 then -1 else
    if i.val = n then 1 else criticalNode n (i.val - 1)

theorem MarkovInterpolationNodes.tau_zero (n : Nat) : tau n 0 = -1 := by
  simp [tau]

theorem MarkovInterpolationNodes.tau_last (n : Nat) (hn : 0 < n) : tau n (Fin.last n) = 1 := by
  simp [tau, Nat.ne_of_gt hn]

theorem MarkovInterpolationNodes.tau_interior {n : Nat} (i : Fin (n + 1))
    (hi0 : 0 < i.val) (hin : i.val < n) :
    tau n i = criticalNode n (i.val - 1) := by
  simp [tau, Nat.ne_of_gt hi0, Nat.ne_of_lt hin]

theorem MarkovInterpolationNodes.criticalNode_lt {n k l : Nat} (hkl : k < l) (hl : l + 1 < n) :
    criticalNode n k < criticalNode n l := by
  have hn : 0 < n := by omega
  have hk : k + 1 < n := by omega
  have hnext : k + 1 <= l := by omega
  have hln : l < n := by omega
  exact ((node_order hn hk).2.2.1.trans_le
    (rootNode_le hnext hln)).trans (node_order hn hl).2.1

theorem MarkovInterpolationNodes.tau_interior_mem_Ioo {n : Nat} (hn : 2 <= n) (i : Fin (n + 1))
    (hi0 : 0 < i.val) (hin : i.val < n) :
    tau n i ∈ Set.Ioo (-1) 1 := by
  rw [tau_interior i hi0 hin]
  exact criticalNode_mem_Ioo (by omega) (by omega)

theorem MarkovInterpolationNodes.tau_strictMono (n : Nat) (hn : 2 <= n) : StrictMono (tau n) := by
  intro i j hij
  have hijv : i.val < j.val := hij
  have hin : i.val < n := by omega
  have hj0 : 0 < j.val := by omega
  have hjle : j.val <= n := Nat.le_of_lt_succ j.isLt
  by_cases hi0 : i.val = 0
  · have hleft : tau n i = -1 := by simp [tau, hi0]
    rw [hleft]
    by_cases hjn : j.val = n
    · have hright : tau n j = 1 := by simp only [tau, if_neg (Nat.ne_of_gt hj0), if_pos hjn]
      rw [hright]
      norm_num
    · exact (tau_interior_mem_Ioo hn j hj0 (by omega)).1
  · have hi0pos : 0 < i.val := by omega
    by_cases hjn : j.val = n
    · have hright : tau n j = 1 := by simp only [tau, if_neg (Nat.ne_of_gt hj0), if_pos hjn]
      rw [hright]
      exact (tau_interior_mem_Ioo hn i hi0pos hin).2
    · have hjnlt : j.val < n := by omega
      rw [tau_interior i hi0pos hin, tau_interior j hj0 hjnlt]
      exact criticalNode_lt (by omega) (by omega)

theorem MarkovInterpolationNodes.tau_injective (n : Nat) (hn : 2 <= n) : Function.Injective (tau n) :=
  (tau_strictMono n hn).injective

theorem MarkovInterpolationNodes.tau_mem_Icc (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    tau n i ∈ Set.Icc (-1) 1 := by
  have hi : (0 : Fin (n + 1)) <= i := Fin.zero_le i
  have hilast : i <= Fin.last n := Fin.le_last i
  have hleft := (tau_strictMono n hn).monotone hi
  have hright := (tau_strictMono n hn).monotone hilast
  rw [tau_zero] at hleft
  rw [tau_last n (by omega)] at hright
  exact ⟨hleft, hright⟩

theorem MarkovInterpolationNodes.abs_chebyshev_eval_neg_one (n : Nat) : |(chebyshev n).eval (-1)| = 1 := by
  have h := T_real_cos Real.pi (n : Int)
  have heval : (chebyshev n).eval (-1) = (-1 : Real) ^ n := by
    simpa only [chebyshev, Real.cos_pi, Int.cast_natCast,
      Real.cos_nat_mul_pi] using h
  rw [heval, abs_pow]
  norm_num

theorem MarkovInterpolationNodes.abs_eval_tau (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    |(chebyshev n).eval (tau n i)| = 1 := by
  by_cases hi0 : i.val = 0
  · simpa only [tau, if_pos hi0] using abs_chebyshev_eval_neg_one n
  · by_cases hin : i.val = n
    · have htau : tau n i = 1 := by simp only [tau, if_neg hi0, if_pos hin]
      rw [htau]
      simp [chebyshev]
    · simpa only [tau, if_neg hi0, if_neg hin] using
        abs_critical_eval n (i.val - 1) (by omega)

theorem MarkovInterpolationNodes.omega_eval_tau (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    (MarkovNodalDegree.omega n).eval (tau n i) = 0 := by
  by_cases hi0 : i.val = 0
  · simp [tau, hi0, MarkovNodalDegree.omega]
  · by_cases hin : i.val = n
    · have htau : tau n i = 1 := by simp only [tau, if_neg hi0, if_pos hin]
      rw [htau]
      simp [MarkovNodalDegree.omega]
    · have hcritical := critical_derivative (n := n) (k := i.val - 1)
        (by omega) (by omega)
      simp only [tau, if_neg hi0, if_neg hin, MarkovNodalDegree.omega,
        eval_mul, eval_sub, eval_pow, eval_X, eval_one]
      change (_ * (chebyshev n).derivative.eval (criticalNode n (i.val - 1))) = 0
      rw [hcritical, mul_zero]

theorem MarkovInterpolationNodes.omega_derivative_eval (n : Nat) (x : Real) :
    (MarkovNodalDegree.omega n).derivative.eval x =
      (n : Real) ^ 2 * (chebyshev n).eval x + x * (chebyshev n).derivative.eval x := by
  have hode := chebyshev_ode_eval n x
  simp only [chebyshev] at hode ⊢
  simp only [MarkovNodalDegree.omega, derivative_mul, derivative_sub,
    derivative_X_sq, derivative_one, sub_zero, eval_add, eval_mul, eval_C,
    eval_X, eval_sub, eval_pow, eval_one]
  linear_combination hode

def MarkovInterpolationNodes.nodeScale (n : Nat) (i : Fin (n + 1)) : Real :=
  if i.val = 0 ∨ i.val = n then 2 * (n : Real) ^ 2 else (n : Real) ^ 2

theorem MarkovInterpolationNodes.nodeScale_pos (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    0 < nodeScale n i := by
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  simp only [nodeScale]
  split_ifs <;> positivity

theorem MarkovInterpolationNodes.omega_derivative_eval_tau (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    (MarkovNodalDegree.omega n).derivative.eval (tau n i) =
      nodeScale n i * (chebyshev n).eval (tau n i) := by
  by_cases hi0 : i.val = 0
  · have hode := chebyshev_ode_eval n (-1)
    have htau : tau n i = -1 := by simp only [tau, if_pos hi0]
    have hscale : nodeScale n i = 2 * (n : Real) ^ 2 := by
      simp only [nodeScale, if_pos (Or.inl hi0)]
    rw [htau, hscale, omega_derivative_eval]
    linear_combination hode
  · by_cases hin : i.val = n
    · have hode := chebyshev_ode_eval n 1
      have htau : tau n i = 1 := by simp only [tau, if_neg hi0, if_pos hin]
      have hscale : nodeScale n i = 2 * (n : Real) ^ 2 := by
        simp only [nodeScale, if_pos (Or.inr hin)]
      rw [htau, hscale, omega_derivative_eval]
      linear_combination hode
    · have hcritical := critical_derivative (n := n) (k := i.val - 1)
        (by omega) (by omega)
      have htau : tau n i = criticalNode n (i.val - 1) := by
        simp only [tau, if_neg hi0, if_neg hin]
      have hscale : nodeScale n i = (n : Real) ^ 2 := by
        simp only [nodeScale, if_neg (not_or.mpr ⟨hi0, hin⟩)]
      rw [htau, hscale, omega_derivative_eval, hcritical, mul_zero, add_zero]

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-interpolation-nodes-unverified-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-interpolation-coefficients-unverified-v1.lean" SHA256 9167fd0f2f0d85105b61322ddf161b837faabcd274a21fd8b7b46cccbc5a0ed2
/- Uncompiled body. Append after MarkovInterpolationNodes, MarkovNodalDegree,
   MarkovNodalFactor, MarkovNodalCoefficient, and MarkovLagrange. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial ShadrinChebyshevNodes

theorem MarkovInterpolationNodes.omega_eq_scaled_nodal (n : Nat) (hn : 2 <= n) :
    MarkovNodalDegree.omega n =
      C (MarkovNodalDegree.omega n).leadingCoeff * Lagrange.nodal Finset.univ (tau n) := by
  apply MarkovNodalFactor.eq_leadingCoeff_mul_nodal
  · exact (tau_injective n hn).injOn
  · have hdegree := MarkovNodalDegree.omega_degree n (by omega)
    simpa only [Finset.card_univ, Fintype.card_fin] using hdegree
  · intro i _
    exact omega_eval_tau n hn i

theorem MarkovInterpolationNodes.coefficient_data (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    MarkovLagrange.denominator Finset.univ (tau n) i ≠ 0 ∧
      (chebyshev n).eval (tau n i) /
          MarkovLagrange.denominator Finset.univ (tau n) i =
        (MarkovNodalDegree.omega n).leadingCoeff / nodeScale n i ∧
      0 < (chebyshev n).eval (tau n i) /
        MarkovLagrange.denominator Finset.univ (tau n) i := by
  exact MarkovNodalCoefficient.coefficient_pos_at_unit_node
    Finset.univ (tau n) (MarkovNodalDegree.omega n) (chebyshev n)
    (MarkovNodalDegree.omega n).leadingCoeff (nodeScale n i)
    (omega_eq_scaled_nodal n hn) i (Finset.mem_univ i)
    (MarkovNodalDegree.omega_leadingCoeff_pos n (by omega))
    (nodeScale_pos n hn i) (abs_eval_tau n hn i) (omega_derivative_eval_tau n hn i)

theorem MarkovInterpolationNodes.coefficient_pos (n : Nat) (hn : 2 <= n) (i : Fin (n + 1)) :
    0 < (chebyshev n).eval (tau n i) /
      MarkovLagrange.denominator Finset.univ (tau n) i :=
  (coefficient_data n hn i).2.2

theorem MarkovInterpolationNodes.derivative_bound_of_common_orientation (n : Nat) (hn : 2 <= n)
    (P : Polynomial Real) (hdegree : P.natDegree <= n)
    (hbounded : ∀ x ∈ Set.Icc (-1 : Real) 1, |P.eval x| <= 1)
    (x sign : Real) (hsign : |sign| = 1)
    (hcommon : ∀ i : Fin (n + 1),
      0 <= sign * (MarkovLagrange.deletedPolynomial Finset.univ (tau n) i).derivative.eval x) :
    |P.derivative.eval x| <= |(chebyshev n).derivative.eval x| := by
  apply MarkovLagrange.derivative_bound_fin n (tau n) (tau_injective n hn)
    P (chebyshev n) hdegree (by simp [chebyshev]) x 1 sign
    (by norm_num) hsign
  · intro i
    exact hbounded (tau n i) (tau_mem_Icc n hn i)
  · exact abs_eval_tau n hn
  · intro i
    simpa only [one_mul] using (coefficient_pos n hn i).le
  · exact hcommon

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-interpolation-coefficients-unverified-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-regional-bounds-unverified-v2.lean" SHA256 56546fe99651ac902d38e55facbbff2e33a47bb7d29ee74ac82b84acbf7c30df
/- Uncompiled body. Append after interpolation nodes and coefficients,
   deleted orientation, nodal factor/degree, comparison intervals/signs,
   and MarkovEndpointBounds. No diagnostic commands are included. -/

set_option autoImplicit false

noncomputable section

section

open Polynomial Set ShadrinChebyshevNodes ShadrinComparisonIntervals
open MarkovInterpolationNodes

theorem ShadrinRegionalBounds.tau_avoided (n : Nat) (hn : 2 <= n) (i : Fin n) (x : Real)
    (hx : x ∈ Icc (left n hn i) (right n hn i))
    (hleft : x ≠ -1) (hright : x ≠ 1) :
    ∀ j : Fin (n + 1), x ≠ tau n j := by
  intro j heq
  by_cases hj0 : j.val = 0
  · apply hleft
    simpa only [tau, if_pos hj0] using heq
  · by_cases hjn : j.val = n
    · apply hright
      simpa only [tau, if_neg hj0, if_pos hjn] using heq
    · let k : Fin (n - 1) := ⟨j.val - 1, by omega⟩
      apply critical_not_mem n hn i k
      change criticalNode n (j.val - 1) ∈ Icc (left n hn i) (right n hn i)
      have hmem : tau n j ∈ Icc (left n hn i) (right n hn i) := heq ▸ hx
      simp only [tau, if_neg hj0, if_neg hjn] at hmem
      exact hmem

theorem ShadrinRegionalBounds.deleted_derivatives_oriented_nonneg (n : Nat) (hn : 2 <= n)
    (i : Fin n) (x : Real)
    (hx : x ∈ Icc (left n hn i) (right n hn i))
    (hleft : x ≠ -1) (hright : x ≠ 1) :
    ∀ j : Fin (n + 1), 0 <= orientation n i.val *
      (MarkovLagrange.deletedPolynomial Finset.univ (tau n) j).derivative.eval x := by
  have hnpos : 0 < n := by omega
  have hdegree : (MarkovNodalDegree.omega n).degree =
      ((Finset.univ : Finset (Fin (n + 1))).card : WithBot Nat) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      MarkovNodalDegree.omega_degree n hnpos
  have hroots : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      (MarkovNodalDegree.omega n).eval (tau n j) = 0 := by
    intro j _
    exact omega_eval_tau n hn j
  have hfactorLeft : MarkovNodalDegree.omega n =
      (X - C (tau n 0)) * ((X - 1) * (chebyshev n).derivative) := by
    rw [tau_zero]
    simp only [MarkovNodalDegree.omega, chebyshev, map_neg, map_one, sub_neg_eq_add]
    ring
  have hfactorRight : MarkovNodalDegree.omega n =
      (X - C (tau n (Fin.last n))) * ((X + 1) * (chebyshev n).derivative) := by
    rw [tau_last n hnpos]
    simp only [MarkovNodalDegree.omega, chebyshev, map_one]
    ring
  have hleftSign : 0 <= orientation n i.val *
      (((X - 1) * (chebyshev n).derivative).derivative).eval x :=
    ShadrinComparisonSigns.minus_nonneg n hn i hx
  have hrightSign : 0 <= orientation n i.val *
      (((X + 1) * (chebyshev n).derivative).derivative).eval x :=
    ShadrinComparisonSigns.plus_nonneg n hn i hx
  have hleftDeleted := MarkovNodalFactor.deleted_derivative_orientation
    Finset.univ (tau n) (MarkovNodalDegree.omega n)
    ((X - 1) * (chebyshev n).derivative)
    (tau_injective n hn).injOn hdegree hroots 0 (Finset.mem_univ 0) hfactorLeft
    (MarkovNodalDegree.omega_leadingCoeff_pos n hnpos) x (orientation n i.val) hleftSign
  have hrightDeleted := MarkovNodalFactor.deleted_derivative_orientation
    Finset.univ (tau n) (MarkovNodalDegree.omega n)
    ((X + 1) * (chebyshev n).derivative)
    (tau_injective n hn).injOn hdegree hroots (Fin.last n)
    (Finset.mem_univ (Fin.last n)) hfactorRight
    (MarkovNodalDegree.omega_leadingCoeff_pos n hnpos) x (orientation n i.val) hrightSign
  have hall := MarkovDeletedOrientation.all_deleted_derivatives_orientation
    Finset.univ (tau n) 0 (Fin.last n) (Finset.mem_univ 0)
    (Finset.mem_univ (Fin.last n)) (tau_zero n) (tau_last n hnpos)
    (fun j _ => tau_mem_Icc n hn j) x (orientation n i.val)
    (fun j _ => tau_avoided n hn i x hx hleft hright j) hleftDeleted hrightDeleted
  intro j
  exact hall j (Finset.mem_univ j)

theorem ShadrinRegionalBounds.derivative_le_chebyshev (n : Nat) (hn : 2 <= n)
    (P : Polynomial Real) (hdegree : P.natDegree <= n)
    (hbound : ∀ y ∈ Icc (-1 : Real) 1, |P.eval y| <= 1)
    (i : Fin n) (x : Real) (hx : x ∈ Icc (left n hn i) (right n hn i)) :
    |P.derivative.eval x| <= |(chebyshev n).derivative.eval x| := by
  by_cases hleft : x = -1
  · subst x
    simpa only [chebyshev] using
      MarkovEndpointBounds.abs_derivative_at_neg_one_le_T P n hdegree hbound
  · by_cases hright : x = 1
    · subst x
      simpa only [chebyshev] using
        MarkovEndpointBounds.abs_derivative_at_one_le_T P n hdegree hbound
    · exact derivative_bound_of_common_orientation n hn P hdegree hbound x
        (orientation n i.val) (abs_orientation n i.val)
        (deleted_derivatives_oriented_nonneg n hn i x hx hleft hright)

end

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-markov-regional-bounds-unverified-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-normalized-assembly-v2.lean" SHA256 d757eebd5dd0a0971dffc0436d32b1ab33b43a3858b7d91331391f961dd7b85a
-- Combine after all checked interpolation, comparison, endpoint, and rescaling helpers.
section

open Polynomial Set ShadrinChebyshevNodes

theorem MarkovNormalizedAssembly.normalized_ge_two (P : Polynomial Real) (n : Nat) (hn : 2 ≤ n)
    (hdegree : P.natDegree ≤ n)
    (hbound : ∀ y ∈ Icc (-1 : Real) 1, |P.eval y| ≤ 1)
    (x : Real) (hx : x ∈ Icc (-1 : Real) 1) :
    |P.derivative.eval x| ≤ (n : Real) ^ 2 := by
  classical
  let l := ShadrinComparisonIntervals.left n hn
  let u := ShadrinComparisonIntervals.right n hn
  let r : Polynomial Real := C ((n : Real) ^ 2) * chebyshev n
  have hcheb : |(chebyshev n).derivative.eval x| ≤ (n : Real) ^ 2 :=
    MarkovChebyshevBounds.abs_derivative_T_le_sq n hx
  have hrbound : |r.eval x| ≤ (n : Real) ^ 2 := by
    simpa only [r, eval_mul, eval_C, chebyshev, MarkovChebyshevBounds.ode_term_T_eq]
      using MarkovChebyshevBounds.abs_ode_term_T_le_sq n hx
  by_cases hinside : ∃ i : Fin n, x ∈ Ioo (l i) (u i)
  · obtain ⟨i, hi⟩ := hinside
    exact (ShadrinRegionalBounds.derivative_le_chebyshev n hn P hdegree hbound i x
      ⟨hi.1.le, hi.2.le⟩).trans hcheb
  · have hout : ∀ i : Fin n, x ∉ Ioo (l i) (u i) := by
      intro i hi
      exact hinside ⟨i, hi⟩
    have hrdegree : r.degree = (n : WithBot Nat) :=
      MarkovChebyshevDegree.squared_nat_chebyshev_degree n (by omega)
    have hsdegree : P.derivative.degree < (n : WithBot Nat) :=
      MarkovChebyshevDegree.derivative_degree_lt_of_natDegree_le P n hdegree
    have hinterval : ∀ i : Fin n, l i < u i :=
      ShadrinComparisonIntervals.interval_nonempty n hn
    have hordered : ∀ i j : Fin n, i < j → u i ≤ l j := by
      intro i j hij
      exact (ShadrinComparisonIntervals.ordered n hn i j hij).le
    have hsign : ∀ i : Fin n,
        (r.eval (l i) < 0 ∧ 0 < r.eval (u i)) ∨
        (0 < r.eval (l i) ∧ r.eval (u i) < 0) := by
      intro i
      simpa only [r, eval_mul, eval_C] using ShadrinComparisonSigns.endpoint_signs n hn i
    have hdom : ∀ i : Fin n,
        |P.derivative.eval (l i)| ≤ |r.eval (l i)| ∧
        |P.derivative.eval (u i)| ≤ |r.eval (u i)| := by
      intro i
      have hleft := ShadrinRegionalBounds.derivative_le_chebyshev n hn P hdegree hbound
        i (l i) ⟨le_rfl, (hinterval i).le⟩
      have hright := ShadrinRegionalBounds.derivative_le_chebyshev n hn P hdegree hbound
        i (u i) ⟨(hinterval i).le, le_rfl⟩
      constructor
      · simpa only [r, eval_mul, eval_C, l, ShadrinComparisonSigns.left_identity, abs_neg]
          using hleft
      · simpa only [r, eval_mul, eval_C, u, ShadrinComparisonSigns.right_identity]
          using hright
    exact (ShadrinRootCount.abs_eval_le_of_ordered_intervals r P.derivative l u
      hrdegree hsdegree hinterval hordered hsign hdom x hout).trans hrbound

theorem MarkovNormalizedAssembly.normalized_one (P : Polynomial Real) (hdegree : P.natDegree ≤ 1)
    (hbound : ∀ y ∈ Icc (-1 : Real) 1, |P.eval y| ≤ 1) (x : Real) :
    |P.derivative.eval x| ≤ (1 : Real) ^ 2 := by
  have hderivativeDegree : P.derivative.natDegree = 0 := by
    have := natDegree_derivative_le P
    omega
  have hconstant : P.derivative = C (P.derivative.coeff 0) :=
    eq_C_of_natDegree_eq_zero hderivativeDegree
  have h := MarkovEndpointBounds.abs_derivative_at_one_le P 1 hdegree hbound
  rw [hconstant, eval_C] at h
  rw [hconstant, eval_C]
  simpa only [Nat.cast_one] using h

theorem MarkovNormalizedAssembly.normalized : MarkovIntervalRescaling.NormalizedMarkov := by
  intro P n hn hdegree hbound x hx
  by_cases hone : n = 1
  · subst n
    simpa only [Nat.cast_one] using normalized_one P hdegree hbound x
  · exact normalized_ge_two P n (by omega) hdegree hbound x hx

theorem MarkovNormalizedAssembly.interval (a b : Real) (hab : a < b) (Q : Polynomial Real) {d : Nat} (M : Real)
    (hdegree : Q.natDegree ≤ d)
    (hbound : ∀ x : Real, a ≤ x → x ≤ b → |Q.eval x| ≤ M) :
    ∀ c : Real, a ≤ c → c ≤ b →
      |Q.derivative.eval c| ≤ 2 * (d : Real) ^ 2 * M / (b - a) :=
  MarkovIntervalRescaling.interval_bound_of_normalized normalized a b hab Q M hdegree hbound

end

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-markov-normalized-assembly-v2.lean"


/-!
# Markov's brothers inequality on a continuous interval

Classical inequality (A. A. Markov, 1889): for univariate real polynomial
`Q` of degree `≤ d` absolutely bounded by `M` on a closed interval
`[a, b]` with `a < b`, the derivative is uniformly bounded by `2 d² M /
(b - a)` on the same interval. The constant `2 d² / (b - a)` is sharp,
achieved by the appropriately scaled Chebyshev polynomial `T_d`.

This is one of the foundational classical results in the theory of
polynomial inequalities, but is *not* present in Mathlib at the
inside-the-interval level (Mathlib has the outside-the-interval extremal
property `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
for `x ≥ 1`, but the inside-the-interval Markov bound requires a separate
argument via Chebyshev expansion + sign analysis).

Left as a platform leaf — DEFERRED. Sub-leaf of `markov_polya_grid`.
Estimated 300-500 lines.
-/

/-- **Markov's brothers inequality on `[a, b]`.**

For real polynomial `Q` of degree `≤ d` with `|Q(x)| ≤ M` for every
`x ∈ [a, b]` (with `a < b`), the derivative satisfies the sharp bound
`|Q'(c)| ≤ 2 d² M / (b - a)` for every `c ∈ [a, b]`. -/
theorem markov_inequality_interval_proof
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (M : ℝ)
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ x : ℝ, a ≤ x → x ≤ b → |Q.eval x| ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 * M / (b - a) := by exact MarkovNormalizedAssembly.interval a b hab Q M h_deg h_bound


theorem solution
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (M : ℝ)
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ x : ℝ, a ≤ x → x ≤ b → |Q.eval x| ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 * M / (b - a) := by exact markov_inequality_interval_proof a b hab Q M h_deg h_bound
