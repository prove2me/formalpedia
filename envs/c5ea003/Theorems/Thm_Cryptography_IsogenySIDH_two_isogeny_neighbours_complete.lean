-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_two_isogeny_neighbours_complete
-- name    : Cryptography.IsogenySIDH.two_isogeny_neighbours_complete
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:43.325846+00:00
-- url     : https://prove2.me/theorems/6282caae-3f4f-4b96-9ae3-4455aa9ebe7e
-- title:
--   Completeness (previous cycle's Conjecture 5).
-- statement:
--   **Completeness (previous cycle's Conjecture 5).**  Let `A` be a Montgomery
--   parameter with `A² ≠ 4` and let `u₁ ≠ u₂` be the two roots of `u² + A²u + A²`.
--   If the three exhibited neighbours `jQuot A`, `jOther A u₁`, `jOther A u₂` are
--   pairwise distinct, then they are *all* the 2-isogeny neighbours of `j(E_A)`:
--   every `Y` with `Φ₂(j(E_A), Y) = 0` is one of them.  Hence the radical formula,
--   applied to the three Montgomery models of `E_A`, misses no 2-isogeny.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_complete[DecidableEq K] {A u₁ u₂ Y : K}
--       (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
--       (hd : A ^ 2 - 4 ≠ 0)
--       (h01 : jQuot A ≠ jOther A u₁) (h02 : jQuot A ≠ jOther A u₂)
--       (h12 : jOther A u₁ ≠ jOther A u₂)
--       (hY : modPoly2 (jMont A) Y = 0) :
--       Y = jQuot A ∨ Y = jOther A u₁ ∨ Y = jOther A u₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean#L188

-- Thm stub generated from Cryptography/IsogenySIDH/TwoIsogenyNeighbours.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
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















/-! ## Completeness of the neighbour list -/

theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_complete[DecidableEq K] {A u₁ u₂ Y : K}
    (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0)
    (h01 : jQuot A ≠ jOther A u₁) (h02 : jQuot A ≠ jOther A u₂)
    (h12 : jOther A u₁ ≠ jOther A u₂)
    (hY : modPoly2 (jMont A) Y = 0) :
    Y = jQuot A ∨ Y = jOther A u₁ ∨ Y = jOther A u₂ := by sorry
