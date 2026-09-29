-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_two_isogeny_neighbours_card_le_three
-- name    : Cryptography.IsogenySIDH.two_isogeny_neighbours_card_le_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:19.907043+00:00
-- url     : https://prove2.me/theorems/2b769fd9-5d65-4249-8472-9a65cdaa14ef
-- title:
--   The 2-isogeny graph is at most 3-regular.
-- statement:
--   **The 2-isogeny graph is at most 3-regular.**  For a fixed `j`, at most
--   three values `j'` satisfy `Φ₂(j, j') = 0`; equivalently, a supersingular curve
--   has at most three 2-isogenous neighbours (counted without multiplicity).  This
--   is the branching bound for radical 2-isogeny walks.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_card_le_three[DecidableEq K] (j : K)
--       (S : Finset K) (hS : ∀ y ∈ S, modPoly2 j y = 0) : S.card ≤ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/ModularTwoIsogeny.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/ModularTwoIsogeny.lean#L257

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








/-! ## The level-2 modular polynomial -/






/-! ## Radical walks are paths in the 2-isogeny graph -/






/-! ## Degree bound: the 2-isogeny graph is cubic -/

theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_card_le_three[DecidableEq K] (j : K)
    (S : Finset K) (hS : ∀ y ∈ S, modPoly2 j y = 0) : S.card ≤ 3 := by sorry
