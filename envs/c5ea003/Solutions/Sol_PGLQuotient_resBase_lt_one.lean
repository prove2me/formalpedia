-- Prove2me | solution 1 for PGLQuotient.resBase_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:28:13.423512+00:00
-- url     : https://prove2.me/submissions/504c378d-090a-43a3-9030-148c9f46fb07

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold

/-!
# The sharp cusp-tail estimate of order `T^{-d}`

For the standard arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`,
with the normalised lattice-minima height `α` of `Algebra.PGLQuotient.VertexModel`, we prove
the two-sided cusp-tail estimate

`c · T^{-d} ≤ mass {α > T} ≤ C · T^{-d}`   for all `T ≥ 1`.

The upper bound is the delicate half: the naive estimate coming from the integrability
threshold only gives `T^{-r}` for every `r < d`.  The sharp exponent is obtained by
*fibering the gap lattice over the height exponent*: the linear form
`N(g) = ∑_k (d-1-k) g_k = d log_q α` determines the first gap coordinate `g_0` once the
remaining coordinates are known, and the residual exponent `R(g) = ∑_k k(d-1-k) g_k` does not
involve `g_0` at all.  Hence `∑_{N(g) = n} q^{-R(g)}` is bounded uniformly in `n`, and
summing the resulting geometric series in `n` produces the exact exponent `T^{-d}`.

The lower bound comes from a single vertex on the cusp ray `λ = (n, 0, …, 0)`.
-/

open PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}



/-! ### The fibering majorant -/









/-! ### From the fibered bound to the sharp `T^{-d}` cusp tail -/






open PGLQuotient in
theorem solution(hq : 1 < q) (k : Fin (d - 1)) : resBase q d k < 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold resBase
  split
  · exact zero_lt_one
  · rename_i hk
    have hk1 : 1 ≤ (k : ℕ) := by omega
    have hkd : 1 ≤ d - 1 - (k : ℕ) := by have := k.isLt; omega
    have h1 : 1 ≤ (k : ℕ) * (d - 1 - (k : ℕ)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : (1:ℝ) < q ^ ((k : ℕ) * (d - 1 - (k : ℕ))) := by
      calc (1:ℝ) = q ^ 0 := (pow_zero q).symm
        _ < q ^ ((k : ℕ) * (d - 1 - (k : ℕ))) := by
            exact pow_lt_pow_right₀ hq (by omega)
    exact inv_lt_one_of_one_lt₀ this
