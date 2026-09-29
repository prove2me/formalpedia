-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_jMont_radTwoParam
-- name    : Cryptography.IsogenySIDH.jMont_radTwoParam
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:41:15.397554+00:00
-- url     : https://prove2.me/theorems/0fb0a18f-d2af-4226-8dbd-6d780383e91f
-- title:
--   The target of the radical step, computed.
-- statement:
--   **The target of the radical step, computed.**  For any square root `α` of
--   `A + 2`, the Montgomery parameter `radTwoParam A α` has `j`-invariant
--   `jQuot A`.  In particular the radical itself disappears from the answer.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.jMont_radTwoParam{A α : K} (htwo : (2 : K) ≠ 0) (hα : α ≠ 0)
--       (hsq : α ^ 2 = A + 2) (hd : A ^ 2 - 4 ≠ 0) :
--       jMont (radTwoParam A α) = jQuot A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/ModularTwoIsogeny.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/ModularTwoIsogeny.lean#L65

-- Thm stub generated from Cryptography/IsogenySIDH/ModularTwoIsogeny.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
/-
# The radical Montgomery step is a genuine edge of the 2-isogeny graph

`RadicalMontgomeryFormula` produced an explicit rational map from `E_A` to a
generalized Montgomery curve with parameter `radTwoParam A α = (A+6)/(2α)`,
`α² = A + 2`.  That is a *local* verification: the formulas transport points.
This file supplies the *global* certificate that the construction really is a
2-isogeny, by checking it against the classical modular polynomial `Φ₂`.

The main results are:

* `jMont_radTwoParam` — the `j`-invariant of the target is
  `jQuot A = 16 (A²+12)³ / (A²-4)²`.  Remarkably the radical `α` cancels: the
  target `j` is a *rational* function of `A`.
* `jMont_model_independent` — the three Montgomery renormalisations of the
  quotient curve (obtained by moving each of its three two-torsion points to
  the origin, using the three radicals `√(A+2)`, `√(2-A)`, `√(A²-4)`) all have
  the same `j`-invariant `jQuot A`.  So the radical step is independent of the
  chosen model and of the sign of the radical.
* `modPoly2_jMont_jQuot` and `modPoly2_radical_step` — the pair
  `(j(E_A), j(E_{A'}))` is a zero of the level-2 modular polynomial `Φ₂`.  This
  is the definitive certificate of 2-isogeny, proved as a polynomial identity
  of degree 54 in `A`.
* `radChain_isTwoIsogenyPath` — an admissible radical walk traces a path in the
  2-isogeny graph, by induction along the walk.
* `two_isogeny_neighbours_card_le_three` — `Φ₂` is monic of degree three in each
  variable, so every vertex of the 2-isogeny graph has at most three neighbours;
  this bounds the branching of a radical walk and is what makes the walk a walk
  on a cubic (Ramanujan) graph.
-/

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## `j`-invariants -/





/-! ## The three Montgomery models of the quotient -/

theorem Cryptography.IsogenySIDH.jMont_radTwoParam{A α : K} (htwo : (2 : K) ≠ 0) (hα : α ≠ 0)
    (hsq : α ^ 2 = A + 2) (hd : A ^ 2 - 4 ≠ 0) :
    jMont (radTwoParam A α) = jQuot A := by sorry
