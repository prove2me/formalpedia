-- Prove2me | Definitions.Def_Novelty_Heegner163
-- name    : Novelty_Heegner163
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:25.551365+00:00
-- url     : https://prove2.me/theorems/f4b3f0d2-8272-45af-abd8-ffee48fe2bec
-- title:
--   Aether Catalog definitions — Novelty_Heegner163
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Heegner163`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Heegner163.lean by skeleton subtraction
import Mathlib
/-
# The unreasonable effectiveness of 163: a verified elementary footprint

The Stark–Heegner theorem and the analytic estimate for `exp (π * sqrt 163)` are
not presently formalized here.  Instead this file proves, without axioms, the
strongest elementary chain directly underlying the phenomenon:

* the exact obstruction ending every Euler-polynomial prime run;
* sharp prime runs for discriminants 43, 67, and 163;
* their exact discriminant correspondence;
* the three exact “cube plus 744” integers supplied by the singular moduli;
* maximality of 163 inside the explicitly enumerated Heegner list.

The last claim is deliberately a theorem about the finite list, not a
formalization of the Stark–Heegner classification.
-/


namespace Heegner163

/-- Euler's quadratic polynomial. -/
def eulerPoly (p n : ℕ) : ℕ := n ^ 2 + n + p

/-- The positive discriminant magnitude associated to `eulerPoly p`. -/
def discriminantMagnitude (p : ℕ) : ℕ := 4 * p - 1

/-- The standard finite list of Heegner numbers.  This definition by itself does
not assert the class-number-one classification. -/
def heegnerNumbers : Finset ℕ := {1, 2, 3, 7, 11, 19, 43, 67, 163}

/-- A prime run is sharp when all values before `p - 1` are prime and the value
at `p - 1` is not prime. -/
def HasSharpEulerRun (p : ℕ) : Prop :=
  (∀ n < p - 1, Nat.Prime (eulerPoly p n)) ∧
    ¬ Nat.Prime (eulerPoly p (p - 1))















end Heegner163


