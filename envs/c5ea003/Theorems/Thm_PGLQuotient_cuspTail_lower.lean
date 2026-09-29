-- Prove2me | Theorems.Thm_PGLQuotient_cuspTail_lower
-- name    : PGLQuotient.cuspTail_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:46:24.83872+00:00
-- url     : https://prove2.me/theorems/9a2e586f-bd9b-4d8f-af89-20429d2c7bc3
-- title:
--   Sharp cusp-tail lower bound: the mass above height `T` is `≫ T^{-d}`.
-- statement:
--   **Sharp cusp-tail lower bound**: the mass above height `T` is `≫ T^{-d}`.
--
--   ```lean
--   theorem PGLQuotient.cuspTail_lower(hq : 1 < q) (hd : 2 ≤ d) :
--       ∃ c > 0, ∀ T : ℝ, 1 ≤ T → c * T ^ (-(d:ℝ)) ≤ cuspTail q d T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/CuspTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/CuspTail.lean#L282

-- Thm stub generated from Algebra/PGLQuotient/CuspTail.lean
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

theorem PGLQuotient.cuspTail_lower(hq : 1 < q) (hd : 2 ≤ d) :
    ∃ c > 0, ∀ T : ℝ, 1 ≤ T → c * T ^ (-(d:ℝ)) ≤ cuspTail q d T := by sorry
