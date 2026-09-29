-- Prove2me | Definitions.Def_Novelty_HeightObstruction
-- name    : Novelty_HeightObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:39.056536+00:00
-- url     : https://prove2.me/theorems/98d473e9-b875-4205-8327-33fedb897e55
-- title:
--   Aether Catalog definitions — Novelty_HeightObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HeightObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HeightObstruction.lean by skeleton subtraction
import Mathlib
/-
# The Global Obstruction as a Néron–Tate Height Pairing

For quotients of higher genus, the generalized Giampietro–Darmon factorization
of the infinite product of `p`-adic cross-ratios into local intersection
multiplicities holds only **up to a global obstruction given by the Néron–Tate
height pairing on the Jacobian**.

The Néron–Tate height is a *positive semidefinite symmetric bilinear form* on
`MW(J) ⊗ ℝ`, positive definite modulo torsion. We model it by a real inner
product on a space `V` (playing the role of `MW(J) ⊗ ℝ`), and we define the
**global obstruction** attached to two Heegner divisors `D, E` by the Gram
determinant of their height pairing:
`Obs(D, E) = ⟨D,D⟩ ⟨E,E⟩ - ⟨D,E⟩²`.

## Main results
* `neronTateObstruction_nonneg` — the global obstruction is always `≥ 0`
  (Cauchy–Schwarz / positivity of the height pairing).
* `sq_real_inner_le` — the underlying Cauchy–Schwarz bound.
* `neronTateObstruction_of_height_zero` — **genus-0 exactness**: if a Heegner
  divisor is a torsion class (height `0`), the obstruction vanishes and the
  factorization is exact.
* `neronTateObstruction_of_parallel` — the obstruction vanishes for proportional
  (linearly dependent) Heegner divisors.
* `neronTateObstruction_symm` — the obstruction is symmetric in `D, E`.
-/

namespace GiampietroDarmon

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **global obstruction** to exact factorization attached to two Heegner
divisors `D, E`, modelled by the Gram determinant of the Néron–Tate height
pairing:
`Obs(D, E) = ⟨D,D⟩ ⟨E,E⟩ - ⟨D,E⟩²`. -/
noncomputable def neronTateObstruction (D E : V) : ℝ :=
  inner ℝ D D * inner ℝ E E - (inner ℝ D E) ^ 2

/-
Cauchy–Schwarz for the (real) height pairing, in squared form.
-/

/-
**Positivity of the global obstruction.** The Néron–Tate height pairing is
positive semidefinite, so the obstruction is always nonnegative.
-/

/-
The global obstruction is symmetric in its two arguments.
-/

/-
**Genus-0 exactness.** If a Heegner divisor `D` is a torsion class — i.e. has
vanishing Néron–Tate height (`‖D‖ = 0`), as happens when the Jacobian of the
quotient is trivial (genus `0`) — then the obstruction vanishes and the
factorization is exact.
-/

/-
The global obstruction vanishes for proportional (linearly dependent) Heegner
divisors `D = t • E`.
-/

end GiampietroDarmon


