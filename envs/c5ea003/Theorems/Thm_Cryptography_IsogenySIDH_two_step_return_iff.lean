-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_two_step_return_iff
-- name    : Cryptography.IsogenySIDH.two_step_return_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:40:53.309792+00:00
-- url     : https://prove2.me/theorems/848aad1c-d25f-4e53-bb90-871681785874
-- title:
--   Two-step return criterion.
-- statement:
--   **Two-step return criterion.**  A radical walk returns to its starting
--   `j`-invariant after two steps exactly when the two explicit polynomials
--   `btNum A` and `btDen A` have the same cube.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.two_step_return_iff{A α : K} (htwo : (2 : K) ≠ 0) (hα : α ≠ 0)
--       (hsq : α ^ 2 = A + 2) (hd : A ^ 2 - 4 ≠ 0) :
--       jQuot (radTwoParam A α) = jMont A ↔ backtrackPoly A = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/RadicalNonBacktracking.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/RadicalNonBacktracking.lean#L97

-- Thm stub generated from Cryptography/IsogenySIDH/RadicalNonBacktracking.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
import Definitions.Def_Cryptography_IsogenySIDH_RadicalNonBacktracking
/-
# Radical 2-isogeny walks do not backtrack on the `j`-line

`RadicalWalkStructure` proved a *one-step* non-backtracking statement at the
level of kernels: the kernel of the next radical step is the image of a
four-torsion point, while the dual kernel is the image of the non-kernel
two-torsion, and these are distinct.  That leaves open the sharper, genuinely
*global* question, which is the one that matters for the mixing behaviour of a
radical walk:

> can a radical walk return to its starting point of the `j`-line after two
> steps, i.e. can `j_{n+2} = j_n`?

This file settles it completely, with no unproved side conditions.

The computation is carried out along the following chain.

* `jQuot_radTwoParam` — the second step's target, as a rational function of the
  *original* parameter:
  `jQuot (radTwoParam A α) = 4 (A² + 60A + 132)³ / ((A+2)(A-2)⁴)`.
  As in `ModularTwoIsogeny`, the radical `α` cancels.
* `two_step_return_iff` — consequently `j_{n+2} = j_n` happens **iff** the two
  explicit polynomials `btNum A = A² + 60A + 132` and
  `btDen A = 4(A²-3)(A-2)` have equal cubes.
* `backtrackPoly_factor` — `btNum³ - btDen³` factors as
  `-(A-6)(4A² + 15A + 18) · (btNum² + btNum·btDen + btDen²)`, the first factor
  being the "principal" branch and the second the branch that needs a
  primitive cube root of unity.
* `jMont_six` (`= 287496`), `jMont_eq_neg3375_of_quadratic` (`= -3375`) and
  `sq_eq_three_of_btDen_eq_zero` (`j = 0`) identify the three exceptional
  `j`-invariants: `287496` (CM by discriminant `-16`), `-3375` (discriminant
  `-7`) and `0` (discriminant `-3`).
* `radical_two_step_backtracking_classification` and the `j`-level corollary
  `radical_two_step_nonbacktracking` — over a field containing no primitive
  cube root of unity, a radical step can backtrack **only** at
  `j ∈ {0, -3375, 287496}`.
* `radChain_two_step_nonbacktracking` — the walk version.
* `backtracking_locus_card_le_nine` — over *any* field (in particular over
  `𝔽_{p²}`, which does contain cube roots of unity) the backtracking locus is
  cut out by a degree-9 polynomial with nonzero leading coefficient `-64`, so
  at most nine Montgomery parameters per field can backtrack.

Together with the results of `RadicalWalkStructure` this closes Conjecture 4 of
the previous cycle's `FUTURE_DIRECTIONS.md` in the two-step case, and pins down
exactly which `j`-invariants the conjectured exceptional set must contain: the
guess `{1728, 8000, -3375, 287496}` was wrong in detail — the correct list for
two-step returns is `{0, -3375, 287496}`, while `{1728, 8000, -3375}` is the
list for one-step returns proved in `RadicalWalkStructure`.
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The two-step target on the `j`-line -/





/-! ## The two-step return criterion -/

theorem Cryptography.IsogenySIDH.two_step_return_iff{A α : K} (htwo : (2 : K) ≠ 0) (hα : α ≠ 0)
    (hsq : α ^ 2 = A + 2) (hd : A ^ 2 - 4 ≠ 0) :
    jQuot (radTwoParam A α) = jMont A ↔ backtrackPoly A = 0 := by sorry
