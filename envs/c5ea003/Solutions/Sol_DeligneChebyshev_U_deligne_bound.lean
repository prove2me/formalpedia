-- Prove2me | solution 1 for DeligneChebyshev.U_deligne_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:37:49.306117+00:00
-- url     : https://prove2.me/submissions/7f4c0476-4100-409f-a256-1ba9e6771f51

-- Sol generated from Algebra/AbstractAlgebra/DeligneChebyshevBound.lean
import Mathlib
import Definitions.Def_Algebra_AbstractAlgebra_DeligneChebyshevBound
import Theorems.Thm_DeligneChebyshev_sin_nat_mul_le

/-!
# The Deligne bound for Chebyshev `U`-polynomials and triple correlation sums

This file proves the (elementary) "Deligne bound" for the Chebyshev polynomials of the
second kind `U_k` on the interval `[-1, 1]`:
`|U_k(x)| ≤ k + 1` for all `x ∈ [-1, 1]`.

The name refers to the analogy with Deligne's bounds for the eigenvalues of Frobenius
(equivalently, for Hecke eigenvalues / Kloosterman-type sums), where the relevant local
factors are exactly Chebyshev `U`-polynomials evaluated on `[-1,1]`.

We also record the immediate application to **triple correlation sums**: any sum
`∑_{n ≤ N} f(n) g(n+1) h(n+2)` of three sequences bounded by `1` in absolute value is
bounded by `N + 1`, and this bound is sharp.

The Chebyshev polynomial is `Polynomial.Chebyshev.U ℝ k`, evaluated via `Polynomial.eval`.
We package this as a real-valued function `Uval k x`.
-/

open Real Set
open scoped BigOperators

open DeligneChebyshev



/-- **Building block 2.** The key Chebyshev–trigonometric identity:
`U_k(cos θ) · sin θ = sin ((k+1) θ)`. -/
theorem U_cos_mul_sin (k : ℕ) (θ : ℝ) :
    Uval k (Real.cos θ) * Real.sin θ = Real.sin ((k + 1) * θ) := by
  unfold Uval
  have := Polynomial.Chebyshev.U_real_cos θ (k : ℤ)
  rw [this]
  push_cast
  ring_nf

/-- **Building block 3a.** `U_k(1) = k + 1`. -/
theorem U_eval_one (n : ℕ) : Uval n 1 = (n + 1 : ℕ) := by
  unfold Uval
  rw [Polynomial.Chebyshev.U_eval_one ℝ (n : ℤ)]
  push_cast; ring

/-- **Building block 3b.** `U_k(-1) = (-1)^k (k + 1)`. -/
theorem U_eval_neg_one (n : ℕ) : Uval n (-1) = (-1 : ℝ) ^ n * (n + 1 : ℕ) := by
  unfold Uval
  rw [Polynomial.Chebyshev.U_eval_neg_one ℝ (n : ℤ)]
  have hpow : ((((n : ℤ)).negOnePow : ℤ) : ℝ) = (-1 : ℝ) ^ n := by
    have hu : ((n : ℤ)).negOnePow = (-1) ^ n := Units.val_inj.mp rfl
    rw [hu]; norm_cast
  rw [hpow]
  push_cast
  ring


/-! ## Triple correlation sums -/





open DeligneChebyshev in
theorem solution(k : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |Uval k x| ≤ (k + 1 : ℕ) := by
  obtain ⟨hx1, hx2⟩ := hx
  -- Step A: write `x = cos θ`.
  set θ : ℝ := Real.arccos x with hθ
  have hcos : Real.cos θ = x := Real.cos_arccos hx1 hx2
  rw [← hcos]
  by_cases h : Real.sin θ = 0
  · -- Case sin θ = 0 : then cos θ = ±1.
    have hsq : Real.cos θ ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [h] at this; nlinarith [this]
    have hcos_eq : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
      rcases mul_eq_zero.mp (by nlinarith [hsq] : (Real.cos θ - 1) * (Real.cos θ + 1) = 0) with
        h1 | h2
      · left; linarith
      · right; linarith
    rcases hcos_eq with hc | hc
    · rw [hc, U_eval_one]
      rw [abs_of_nonneg (by positivity)]
    · rw [hc, U_eval_neg_one]
      rw [abs_mul, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg (by positivity)]
  · -- Case sin θ ≠ 0 : `U_k(cos θ) = sin((k+1)θ)/sin θ`.
    have hkey : Uval k (Real.cos θ) * Real.sin θ = Real.sin ((k + 1) * θ) :=
      U_cos_mul_sin k θ
    have habs : |Uval k (Real.cos θ)| * |Real.sin θ| = |Real.sin ((k + 1) * θ)| := by
      rw [← abs_mul, hkey]
    have hnum : |Real.sin ((k + 1) * θ)| ≤ (k + 1 : ℕ) * |Real.sin θ| := by
      have hs := sin_nat_mul_le (k + 1) θ
      push_cast at hs ⊢
      exact hs
    have hpos : 0 < |Real.sin θ| := abs_pos.mpr h
    have : |Uval k (Real.cos θ)| * |Real.sin θ| ≤ ((k + 1 : ℕ)) * |Real.sin θ| := by
      rw [habs]; exact hnum
    exact le_of_mul_le_mul_right this hpos
