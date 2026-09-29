-- Prove2me | solution 1 for PGLQuotient.height_gt_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:18:14.278048+00:00
-- url     : https://prove2.me/submissions/91aa5d37-8a3a-444f-8d7c-899611999b27

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel

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
theorem solution(hq : 1 < q) (hd : 2 ≤ d) {T : ℝ} (hT : 1 ≤ T) (g : Vertex d) :
    T < height q g ↔ (d : ℝ) * Real.logb q T < heightExp g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hTq : q ^ (Real.logb q T) = T := Real.rpow_logb hq0 (ne_of_gt hq) hT0
  constructor
  · intro h
    rw [← hTq] at h
    have h2 := (Real.rpow_lt_rpow_left_iff hq).mp h
    rw [lt_div_iff₀ hd0] at h2
    linarith
  · intro h
    rw [← hTq]
    refine (Real.rpow_lt_rpow_left_iff hq).mpr ?_
    rw [lt_div_iff₀ hd0]
    linarith
