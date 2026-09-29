-- Prove2me | solution 1 for Cryptography.IsogenySIDH.jMont_radTwoParamMinus
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:39:20.411125+00:00
-- url     : https://prove2.me/submissions/49383c0d-8418-4ea7-ad33-a8072ea18b51

-- Sol generated from Cryptography/IsogenySIDH/ModularTwoIsogeny.lean
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






/-! ## How many Montgomery models does one `j`-invariant have? -/








open Cryptography.IsogenySIDH in
theorem solution{A γ : K} (htwo : (2 : K) ≠ 0) (hγ : γ ≠ 0)
    (hsq : γ ^ 2 = 2 - A) (hd : A ^ 2 - 4 ≠ 0) :
    jMont (radTwoParamMinus A γ) = jQuot A := by
  have hfour : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero htwo htwo
  have hγ2 : γ ^ 2 ≠ 0 := pow_ne_zero 2 hγ
  have hAp2 : A + 2 ≠ 0 := fun h => hd (by linear_combination (A - 2) * h)
  have hnum : ((A - 6) / (2 * γ)) ^ 2 - 3 = (A ^ 2 + 12) / (4 * γ ^ 2) := by
    field_simp; linear_combination (-48 : K) * hsq
  have hden : ((A - 6) / (2 * γ)) ^ 2 - 4 = (A + 2) ^ 2 / (4 * γ ^ 2) := by
    field_simp; linear_combination (-64 : K) * hsq
  have h4 : (A ^ 2 - 4) ^ 2 = (γ ^ 2) ^ 2 * (A + 2) ^ 2 := by
    rw [hsq]; ring
  simp only [jMont, jQuot, radTwoParamMinus, hnum, hden, h4]
  field_simp
  ring
