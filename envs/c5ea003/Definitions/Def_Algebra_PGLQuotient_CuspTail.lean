-- Prove2me | Definitions.Def_Algebra_PGLQuotient_CuspTail
-- name    : Algebra_PGLQuotient_CuspTail
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:28:20.528882+00:00
-- url     : https://prove2.me/theorems/e5268184-cc4f-426f-b5cd-dcf4e9e1561a
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_CuspTail
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.CuspTail`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/CuspTail.lean by skeleton subtraction
import Mathlib
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

namespace PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}

/-- The cusp-tail mass at height level `T`. -/
noncomputable def cuspTail (q : ℝ) (d : ℕ) (T : ℝ) : ℝ :=
  ∑' g : {g : Vertex d | T < height q g}, vertexWeight q (g : Vertex d)


/-! ### The fibering majorant -/

/-- The per-coordinate base of the residual geometric series: the coordinate `k = 0`
is switched off, since the residual exponent `R` does not involve it. -/
noncomputable def resBase (q : ℝ) (d : ℕ) (k : Fin (d - 1)) : ℝ :=
  if (k : ℕ) = 0 then 0 else (q ^ ((k : ℕ) * (d - 1 - (k : ℕ))))⁻¹








/-! ### From the fibered bound to the sharp `T^{-d}` cusp tail -/





end PGLQuotient


