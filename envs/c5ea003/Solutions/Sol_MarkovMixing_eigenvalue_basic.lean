-- Prove2me | solution 1 for MarkovMixing.eigenvalue_basic
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:27:31.258491+00:00
-- url     : https://prove2.me/submissions/7e6dfcc9-9d86-4703-bce1-d7f6cda44542

import Theorems.Thm_MarkovMixing_harmonic_eq_const
import Theorems.Thm_MarkovMixing_exists_pow_pos
import Definitions.Def_mm_spectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) :
    (∀ lam : ℝ, IsEigenvalue P lam → |lam| ≤ 1) ∧
    (MarkovMixing.Irreducible P → ∀ f : V → ℝ, P.mulVec f = f → ∀ x y : V, f x = f y) ∧
    (MarkovMixing.Irreducible P → Aperiodic P → ¬ IsEigenvalue P (-1)) := by
  classical
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
  refine ⟨?_, ?_, ?_⟩
  · -- (i) every eigenvalue has modulus at most one
    rintro lam ⟨f, hfne, hf⟩
    obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfne (funext hcon)
    haveI : Nonempty V := ⟨z⟩
    obtain ⟨x₀, -, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V) (fun x => |f x|) Finset.univ_nonempty
    have hmax' : ∀ w : V, |f w| ≤ |f x₀| := fun w => hmax w (Finset.mem_univ w)
    have hx₀pos : 0 < |f x₀| :=
      lt_of_lt_of_le (abs_pos.mpr hz) (hmax' z)
    have hval : lam * f x₀ = ∑ y, P x₀ y * f y := by
      have h := congrFun hf x₀
      show lam * f x₀ = (P.mulVec f) x₀
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul]
    have hbound : |lam| * |f x₀| ≤ |f x₀| := by
      rw [← abs_mul, hval]
      calc |∑ y, P x₀ y * f y| ≤ ∑ y, |P x₀ y * f y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, P x₀ y * |f x₀| := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_of_nonneg (hP.1 x₀ y)]
            exact mul_le_mul_of_nonneg_left (hmax' y) (hP.1 x₀ y)
        _ = |f x₀| := by rw [← Finset.sum_mul, hP.2 x₀, one_mul]
    nlinarith [hbound, hx₀pos]
  · -- (ii) eigenfunctions of eigenvalue one are constant
    intro hirr f hf x y
    have hharm : Harmonic P f := by
      intro w
      have h := congrFun hf w
      exact h.symm
    exact MarkovMixing.harmonic_eq_const P hP hirr f hharm x y
  · -- (iii) `-1` is not an eigenvalue of an irreducible aperiodic chain
    rintro hirr hap ⟨f, hfne, hf⟩
    have hfneg : P.mulVec f = -f := by
      rw [hf]
      funext w
      simp
    rcases isEmpty_or_nonempty V with hV | hV
    · exact hfne (funext fun w => (IsEmpty.false w).elim)
    obtain ⟨r, hr0, hrpos⟩ := MarkovMixing.exists_pow_pos P hP hirr hap
    -- the doubled power is positive and fixes `f`
    set R : ℕ := 2 * r with hR
    have hRpos : ∀ x y : V, 0 < (P ^ R) x y := by
      intro x y
      have hsplit : (P ^ R) x y = ∑ z, (P ^ r) x z * (P ^ r) z y := by
        rw [hR, two_mul, pow_add]; rfl
      rw [hsplit]
      refine Finset.sum_pos (fun z _ => mul_pos (hrpos x z) (hrpos z y)) ?_
      exact ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    have hiter : ∀ n : ℕ, (P ^ n).mulVec f = ((-1 : ℝ) ^ n) • f := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ← Matrix.mulVec_mulVec, hfneg]
          have : (P ^ m).mulVec (-f) = -((P ^ m).mulVec f) := by
            funext w
            show ∑ y, (P ^ m) w y * (-f y) = -∑ y, (P ^ m) w y * f y
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun y _ => by ring
          rw [this, ih]
          funext w
          simp [pow_succ]
    have hfix : (P ^ R).mulVec f = f := by
      rw [hiter R, hR]
      have : ((-1 : ℝ) ^ (2 * r)) = 1 := by
        rw [pow_mul]
        norm_num
      rw [this, one_smul]
    -- `P ^ R` is stochastic and irreducible, so `f` is constant
    have hstochR : IsStochastic (P ^ R) := ⟨fun a b => hpow_nonneg R a b, hpow_row R⟩
    have hirrR : MarkovMixing.Irreducible (P ^ R) := by
      intro a b
      exact ⟨1, by rw [pow_one]; exact hRpos a b⟩
    have hharmR : Harmonic (P ^ R) f := by
      intro w
      exact (congrFun hfix w).symm
    have hconst : ∀ a b : V, f a = f b :=
      fun a b => MarkovMixing.harmonic_eq_const (P ^ R) hstochR hirrR f hharmR a b
    -- a constant eigenfunction of eigenvalue `-1` must vanish
    set x₀ : V := Classical.arbitrary V with hx₀
    have hcv : ∀ w : V, f w = f x₀ := fun w => hconst w x₀
    have hzero : f x₀ = - f x₀ := by
      have h := congrFun hfneg x₀
      show f x₀ = -f x₀
      have hlhs : (P.mulVec f) x₀ = f x₀ := by
        show ∑ y, P x₀ y * f y = f x₀
        rw [Finset.sum_congr rfl fun y _ => by rw [hcv y], ← Finset.sum_mul, hP.2 x₀, one_mul]
      rw [hlhs] at h
      simpa using h
    have : f x₀ = 0 := by linarith
    exact hfne (funext fun w => by rw [hcv w, this]; rfl)
