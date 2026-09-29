-- Prove2me | Definitions.Def_Probability_ForkPinningSemiprime
-- name    : Probability_ForkPinningSemiprime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:45.771267+00:00
-- url     : https://prove2.me/theorems/ea48471c-4c0e-4a27-b1b4-bf15a36f8656
-- title:
--   Aether Catalog definitions — Probability_ForkPinningSemiprime
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningSemiprime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningSemiprime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ForkPinningGalois
/-
# The semiprime level: a 100%-pinned prime-level fork collapses to a 0.07-bit dial

For the cyclic cubic field of conductor 7 the prime-level fork is *deterministic* given
`p mod 7`.  Take a semiprime `N = p q` with `p`, `q` independent.  What the residue of `N`
records is the **product** of the two cubic-residue characters, and the accessible fork is the
disjunction `OR = [p splits] ∨ [q splits]`.

The model is therefore the uniform measure on `C₃ × C₃` (the pair of Frobenius elements),
with

* observable `cubicClassOfN (a, b) = a + b`  (the cubic-residue class of `N` mod 7),
* fork `splitOR (a, b) = [a = 0 ∨ b = 0]`,
* factor label `firstFactorSplits (a, b) = [a = 0]`.

Results:

* `ForkPinning.semiprime_OR_mutualInfo` :
  `I(N mod 7 ; OR) = log 3 − (5/9) log 5 − (2/9) log 2` = 0.0728 bits
  (the measured value was 0.0718, the predicted 0.0728);
* `ForkPinning.semiprime_collapse` : the semiprime-level information is less than a twelfth of
  the prime-level information `log 3 − (2/3) log 2` = 0.9183 bits;
* `ForkPinning.which_factor_wall` : `I(N mod 7 ; which factor splits) = 0` — **exactly zero**,
  the "which-factor wall" (measured `0.0001`).
-/


namespace ForkPinning

open Finset Real

/-! ## Sums over `C₃` -/


variable {Ω : Type*} [Fintype Ω]



/-! ## The semiprime model -/

/-- The cubic-residue class of `N = p q`: the product of the two prime classes. -/
def cubicClassOfN (x : ZMod 3 × ZMod 3) : ZMod 3 := x.1 + x.2

/-- `OR = [p splits] ∨ [q splits]`. -/
def splitOR (x : ZMod 3 × ZMod 3) : Bool := decide (x.1 = 0 ∨ x.2 = 0)

/-- Which factor splits: the label the factoring problem actually needs. -/
def firstFactorSplits (x : ZMod 3 × ZMod 3) : Bool := decide (x.1 = 0)














/-! ## The which-factor wall -/




end ForkPinning


