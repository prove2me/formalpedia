-- Prove2me | solution 1 for LinearOptimization.interior_point_kkt_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-08-06T21:19:50.782103+00:00
-- url     : https://prove2.me/submissions/43665a52-db15-4303-9355-29567ecf1877

import Definitions.Def_LinearOptimization_LogBarrier_CentralPath

/-!
# Lemma 9.5 (Bertsimas & Tsitsiklis, p. 421)

A KKT point of the barrier problem minimizes the primal barrier (uniquely) and
maximizes the dual barrier.

Both halves reduce to the elementary inequality `log t ≤ t − 1`, strict unless
`t = 1`: with `x*ⱼ s*ⱼ = μ`,

`B_μ(x) − B_μ(x*) = μ ∑ⱼ (tⱼ − 1 − log tⱼ)`,  `tⱼ = xⱼ / x*ⱼ`,

and dually with `tⱼ = sⱼ / s*ⱼ`.
-/

open Matrix

namespace KKT

open LinearOptimization

variable {m n : ℕ}

/-- Moving a matrix across a dot product. -/
lemma transpose_dot (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) (y : Fin n → ℝ) :
    (Aᵀ.mulVec q) ⬝ᵥ y = q ⬝ᵥ (A.mulVec y) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- `t − 1 − log t ≥ 0` for `t > 0`, with equality only at `t = 1`. -/
lemma sub_one_sub_log_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ t - 1 - Real.log t := by
  have := Real.log_le_sub_one_of_pos ht
  linarith

lemma sub_one_sub_log_pos {t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) : 0 < t - 1 - Real.log t := by
  have := Real.log_lt_sub_one_of_pos ht h1
  linarith

end KKT

open LinearOptimization KKT
open Matrix

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (mu : ℝ) (hmu : 0 < mu)
    (xstar : Fin n → ℝ) (pstar : Fin m → ℝ) (sstar : Fin n → ℝ)
    (hkkt : IsCentralPathPoint A b c mu xstar pstar sstar) :
    (∀ x : Fin n → ℝ, A.mulVec x = b → (∀ j, 0 < x j) →
      logBarrier c mu xstar ≤ logBarrier c mu x ∧
        (logBarrier c mu x = logBarrier c mu xstar → x = xstar)) ∧
    (∀ (p : Fin m → ℝ) (s : Fin n → ℝ), Aᵀ.mulVec p + s = c →
      (∀ j, 0 < s j) →
      dualLogBarrier b mu p s ≤ dualLogBarrier b mu pstar sstar) := by
  obtain ⟨hAx, hxnn, hAps, hsnn, hcomp⟩ := hkkt
  -- the central-path point is strictly positive
  have hxpos : ∀ j, 0 < xstar j := by
    intro j
    rcases lt_or_eq_of_le (hxnn j) with h | h
    · exact h
    · exfalso
      have hj := hcomp j
      rw [← h] at hj
      have h0 : (0 : ℝ) = mu := by simpa using hj
      linarith
  have hspos : ∀ j, 0 < sstar j := by
    intro j
    rcases lt_or_eq_of_le (hsnn j) with h | h
    · exact h
    · exfalso
      have hj := hcomp j
      rw [← h] at hj
      have h0 : (0 : ℝ) = mu := by simpa using hj
      linarith
  constructor
  · -- primal: `x*` minimizes the barrier, uniquely
    intro x hAxb hxpos'
    -- the key pointwise identity
    have hkey : logBarrier c mu x - logBarrier c mu xstar
        = mu * ∑ j, (x j / xstar j - 1 - Real.log (x j / xstar j)) := by
      have hc : c ⬝ᵥ x - c ⬝ᵥ xstar = ∑ j, sstar j * (x j - xstar j) := by
        have hsplit : ∀ y : Fin n → ℝ, A.mulVec y = b →
            c ⬝ᵥ y = pstar ⬝ᵥ b + sstar ⬝ᵥ y := by
          intro y hy
          rw [← hAps, add_dotProduct, transpose_dot, hy]
        rw [hsplit x hAxb, hsplit xstar hAx]
        have hcancel : (pstar ⬝ᵥ b + sstar ⬝ᵥ x) - (pstar ⬝ᵥ b + sstar ⬝ᵥ xstar)
            = sstar ⬝ᵥ x - sstar ⬝ᵥ xstar := by ring
        rw [hcancel]
        simp only [dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hterm : ∀ j, sstar j * (x j - xstar j) - mu * (Real.log (x j) - Real.log (xstar j))
          = mu * (x j / xstar j - 1 - Real.log (x j / xstar j)) := by
        intro j
        have hxs : sstar j = mu / xstar j := by
          rw [eq_div_iff (ne_of_gt (hxpos j)), mul_comm]
          exact hcomp j
        have hlog : Real.log (x j / xstar j) = Real.log (x j) - Real.log (xstar j) :=
          Real.log_div (ne_of_gt (hxpos' j)) (ne_of_gt (hxpos j))
        have hne : xstar j ≠ 0 := ne_of_gt (hxpos j)
        rw [hxs, hlog]
        field_simp
      simp only [logBarrier]
      have hsplit : c ⬝ᵥ x - mu * ∑ j, Real.log (x j)
          - (c ⬝ᵥ xstar - mu * ∑ j, Real.log (xstar j))
          = (c ⬝ᵥ x - c ⬝ᵥ xstar) - mu * ∑ j, (Real.log (x j) - Real.log (xstar j)) := by
        rw [Finset.sum_sub_distrib]; ring
      rw [hsplit, hc, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => hterm j)
    have hpos : ∀ j, 0 < x j / xstar j := fun j => div_pos (hxpos' j) (hxpos j)
    have hnn : 0 ≤ ∑ j, (x j / xstar j - 1 - Real.log (x j / xstar j)) :=
      Finset.sum_nonneg (fun j _ => sub_one_sub_log_nonneg (hpos j))
    refine ⟨by nlinarith [hkey], ?_⟩
    intro heq
    -- equality forces every ratio to be `1`
    have hzero : ∑ j, (x j / xstar j - 1 - Real.log (x j / xstar j)) = 0 := by
      have : mu * ∑ j, (x j / xstar j - 1 - Real.log (x j / xstar j)) = 0 := by
        rw [← hkey, heq]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (ne_of_gt hmu)
      · exact h
    funext j
    by_contra hne
    have hne1 : x j / xstar j ≠ 1 := by
      intro h
      apply hne
      have hxne : xstar j ≠ 0 := ne_of_gt (hxpos j)
      field_simp at h
      exact h
    have hjpos : 0 < x j / xstar j - 1 - Real.log (x j / xstar j) :=
      sub_one_sub_log_pos (hpos j) hne1
    have hsum : 0 < ∑ j, (x j / xstar j - 1 - Real.log (x j / xstar j)) := by
      refine lt_of_lt_of_le hjpos ?_
      exact Finset.single_le_sum
        (fun i _ => sub_one_sub_log_nonneg (hpos i)) (Finset.mem_univ j)
    rw [hzero] at hsum
    exact lt_irrefl 0 hsum
  · -- dual: `(p*, s*)` maximizes the dual barrier
    intro p s hAps' hspos'
    have hkey : dualLogBarrier b mu pstar sstar - dualLogBarrier b mu p s
        = mu * ∑ j, (s j / sstar j - 1 - Real.log (s j / sstar j)) := by
      have hb : pstar ⬝ᵥ b - p ⬝ᵥ b = ∑ j, xstar j * (s j - sstar j) := by
        have hbx : ∀ q : Fin m → ℝ, q ⬝ᵥ b = ∑ j, Aᵀ.mulVec q j * xstar j := by
          intro q
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have : b i = ∑ j, A i j * xstar j := by rw [← hAx]; rfl
          rw [this, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hbx pstar, hbx p, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h1 : Aᵀ.mulVec pstar j = c j - sstar j := by
          have := congrFun hAps j
          simp only [Pi.add_apply] at this
          linarith
        have h2 : Aᵀ.mulVec p j = c j - s j := by
          have := congrFun hAps' j
          simp only [Pi.add_apply] at this
          linarith
        rw [h1, h2]; ring
      have hterm : ∀ j, xstar j * (s j - sstar j) + mu * (Real.log (sstar j) - Real.log (s j))
          = mu * (s j / sstar j - 1 - Real.log (s j / sstar j)) := by
        intro j
        have hxs : xstar j = mu / sstar j := by
          rw [eq_div_iff (ne_of_gt (hspos j))]
          exact hcomp j
        have hlog : Real.log (s j / sstar j) = Real.log (s j) - Real.log (sstar j) :=
          Real.log_div (ne_of_gt (hspos' j)) (ne_of_gt (hspos j))
        have hne : sstar j ≠ 0 := ne_of_gt (hspos j)
        rw [hxs, hlog]
        field_simp
        ring
      simp only [dualLogBarrier]
      have hsplit : pstar ⬝ᵥ b + mu * ∑ j, Real.log (sstar j)
          - (p ⬝ᵥ b + mu * ∑ j, Real.log (s j))
          = (pstar ⬝ᵥ b - p ⬝ᵥ b) + mu * ∑ j, (Real.log (sstar j) - Real.log (s j)) := by
        rw [Finset.sum_sub_distrib]; ring
      rw [hsplit, hb, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => hterm j)
    have hpos : ∀ j, 0 < s j / sstar j := fun j => div_pos (hspos' j) (hspos j)
    have hnn : 0 ≤ ∑ j, (s j / sstar j - 1 - Real.log (s j / sstar j)) :=
      Finset.sum_nonneg (fun j _ => sub_one_sub_log_nonneg (hpos j))
    nlinarith [hkey]
