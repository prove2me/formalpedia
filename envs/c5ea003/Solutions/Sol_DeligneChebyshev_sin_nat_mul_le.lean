-- Prove2me | solution 1 for DeligneChebyshev.sin_nat_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:24:54.443738+00:00
-- url     : https://prove2.me/submissions/71b0bd97-d1a3-4085-9534-00b38bcee367

-- Sol generated from Algebra/AbstractAlgebra/DeligneChebyshevBound.lean
import Mathlib
import Definitions.Def_Algebra_AbstractAlgebra_DeligneChebyshevBound

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







/-! ## Triple correlation sums -/





open DeligneChebyshev in
theorem solution: ∀ (n : ℕ) (θ : ℝ), |Real.sin (n * θ)| ≤ n * |Real.sin θ| := by
  intro n θ
  induction n with
  | zero => simp
  | succ m ih =>
      have hstep : Real.sin ((m + 1 : ℕ) * θ)
          = Real.sin (m * θ) * Real.cos θ + Real.cos (m * θ) * Real.sin θ := by
        have : ((m + 1 : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ := by push_cast; ring
        rw [this, Real.sin_add]
      rw [hstep]
      calc |Real.sin (m * θ) * Real.cos θ + Real.cos (m * θ) * Real.sin θ|
          ≤ |Real.sin (m * θ) * Real.cos θ| + |Real.cos (m * θ) * Real.sin θ| :=
            abs_add_le _ _
        _ = |Real.sin (m * θ)| * |Real.cos θ| + |Real.cos (m * θ)| * |Real.sin θ| := by
            rw [abs_mul, abs_mul]
        _ ≤ |Real.sin (m * θ)| * 1 + 1 * |Real.sin θ| := by
            gcongr
            · exact Real.abs_cos_le_one θ
            · exact Real.abs_cos_le_one _
        _ ≤ (m : ℝ) * |Real.sin θ| * 1 + 1 * |Real.sin θ| := by
            gcongr
        _ = ((m + 1 : ℕ) : ℝ) * |Real.sin θ| := by push_cast; ring
