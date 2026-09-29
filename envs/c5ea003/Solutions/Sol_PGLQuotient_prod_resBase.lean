-- Prove2me | solution 1 for PGLQuotient.prod_resBase
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:28:14.685925+00:00
-- url     : https://prove2.me/submissions/b2b746b0-8ba5-4937-bd35-6fa21d732f64

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapAt_coe

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
theorem solution(hq : 1 < q) (g : Vertex d) (h0 : 0 < d - 1) :
    ∏ k, resBase q d k ^ (Function.update g ⟨0, h0⟩ 0 k) = (q ^ resExp g)⁻¹ := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hterm : ∀ k : Fin (d - 1), resBase q d k ^ (Function.update g ⟨0, h0⟩ 0 k)
      = (q⁻¹) ^ ((k : ℕ) * (d - 1 - (k : ℕ)) * g k) := by
    intro k
    by_cases hk : k = ⟨0, h0⟩
    · subst hk
      simp [resBase]
    · have hk0 : (k : ℕ) ≠ 0 := by
        intro hc
        exact hk (Fin.ext hc)
      rw [Function.update_of_ne hk, resBase, if_neg hk0, ← inv_pow, ← pow_mul]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_pow_eq_pow_sum, ← inv_pow]
  congr 1
  rw [resExp, ← Fin.sum_univ_eq_sum_range (fun k => k * (d - 1 - k) * gapAt g k)]
  exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe])
