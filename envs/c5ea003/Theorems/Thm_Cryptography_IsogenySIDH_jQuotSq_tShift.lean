-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_jQuotSq_tShift
-- name    : Cryptography.IsogenySIDH.jQuotSq_tShift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:42:42.20971+00:00
-- url     : https://prove2.me/theorems/b9616854-f900-43c4-9f64-8fe47bd9313c
-- title:
--   The radical step applied to the shifted model produces `jOther A u`.
-- statement:
--   The radical step applied to the shifted model produces `jOther A u`.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.jQuotSq_tShift{A u : K} (hu : u ^ 2 + A ^ 2 * u + A ^ 2 = 0)
--       (hd : A ^ 2 - 4 ≠ 0) : jQuotSq (tShift A u) = jOther A u := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean#L166

-- Thm stub generated from Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_RadicalNonBacktracking
import Definitions.Def_Cryptography_IsogenySIDH_TwoIsogenyNeighbours
/-
# The three 2-isogenous neighbours of a Montgomery curve, explicitly

`ModularTwoIsogeny` computed the neighbour reached by the *radical* step — the
quotient of `E_A : y² = x³ + Ax² + x` by the rational two-torsion point `(0,0)`,
whose `j`-invariant is the rational function `jQuot A = 16(A²+12)³/(A²-4)²` —
and bounded the number of neighbours by three.  It did **not** say what the two
remaining neighbours are, so the possibility remained that the radical formulas
miss some 2-isogenies.  This file removes that gap; it is the previous cycle's
Conjecture 5 ("every Montgomery 2-neighbour arises radically").

The other two two-torsion points of `E_A` are `(r, 0)` with `r² + Ar + 1 = 0`.
Moving `(r,0)` to the origin gives another Montgomery model of the *same* curve,
whose parameter squared is

  `tShift A u = (A² - 3u - 9) / (-(u+2))`,   `u = A·r`,

and `u` is then a root of the *rational* quadratic `u² + A²u + A² = 0` — so the
two extra neighbours are conjugate over `K(√(A²-4))`, exactly as the geometry
predicts.  Feeding that model into the radical formula gives the neighbour

  `jOther A u = 16 (A² - 15u - 33)³ / ((-(u+2)) (A² + u - 1)²)`.

Results:

* `jMontSq`, `jQuotSq` — the observation, used implicitly in `ModularTwoIsogeny`,
  that both `j`-invariants depend on `A` only through `A²`; this is what lets us
  work with the *square* of the shifted Montgomery parameter and thereby avoid
  the square root `√(-Ar-2)` that the shifted model itself requires.
* `two_torsion_shift_j_invariant` — `jMontSq (tShift A u) = jMont A`: the shifted
  model really is a model of the same curve.  (Key identity:
  `(u+2)²(A²+u-1) = A²-4` modulo `u² + A²u + A² = 0`.)
* `modPoly2_jMont_jOther` — `Φ₂(j(E_A), jOther A u) = 0`: the two extra
  neighbours are genuine 2-isogeny neighbours.
* `two_isogeny_neighbours_complete` — **completeness**: if the three exhibited
  neighbours are pairwise distinct, then *every* solution of
  `Φ₂(j(E_A), Y) = 0` is one of them.  So the radical formula together with the
  two-torsion shift generates the whole 2-isogeny neighbourhood, and nothing is
  missed.
* `u_of_two_torsion`, `u_sum`, `u_prod`, `u_exists_iff_sq` — the dictionary
  between the two-torsion abscissa `r` and the parameter `u = A·r`, including
  the fact that the extra neighbours exist over `K` exactly when `A²(A²-4)` is a
  square, i.e. over `K(√(A²-4))`.
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## Both `j`-invariants depend only on `A²` -/






/-! ## The two-torsion shift -/

theorem Cryptography.IsogenySIDH.jQuotSq_tShift{A u : K} (hu : u ^ 2 + A ^ 2 * u + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0) : jQuotSq (tShift A u) = jOther A u := by sorry
