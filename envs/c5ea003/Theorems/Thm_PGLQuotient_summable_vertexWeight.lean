-- Prove2me | Theorems.Thm_PGLQuotient_summable_vertexWeight
-- name    : PGLQuotient.summable_vertexWeight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:46:28.983492+00:00
-- url     : https://prove2.me/theorems/f2424789-93e0-472c-8885-5cc8a409606e
-- title:
--   Summable vertexWeight
-- statement:
--   Formal statement of `PGLQuotient.summable_vertexWeight` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PGLQuotient.summable_vertexWeight(hq : 1 < q) (hd : 2 ≤ d) :
--       Summable (fun g : Vertex d => vertexWeight q g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/CuspTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/CuspTail.lean#L32

-- Thm stub generated from Algebra/PGLQuotient/CuspTail.lean
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

theorem PGLQuotient.summable_vertexWeight(hq : 1 < q) (hd : 2 ≤ d) :
    Summable (fun g : Vertex d => vertexWeight q g) := by sorry
