-- Prove2me | Theorems.Thm_ForkPinning_semiprime_OR_mutualInfo
-- name    : ForkPinning.semiprime_OR_mutualInfo
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:36.480635+00:00
-- url     : https://prove2.me/theorems/dda764f7-c13d-4a59-b549-1e4aeed80aa8
-- title:
--   The semiprime-level dial.
-- statement:
--   **The semiprime-level dial.**  `I(N mod 7 ; OR) = log 3 − (5/9) log 5 − (2/9) log 2`,
--   i.e. `0.0728` bits (measured: `0.0718`).
--
--   ```lean
--   theorem ForkPinning.semiprime_OR_mutualInfo:
--       mutualInfo cubicClassOfN splitOR
--         = Real.log 3 - (5 / 9) * Real.log 5 - (2 / 9) * Real.log 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningSemiprime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningSemiprime.lean#L110

-- Thm stub generated from Probability/ForkPinningSemiprime.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
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


open ForkPinning

open Finset Real

/-! ## Sums over `C₃` -/


variable {Ω : Type*} [Fintype Ω]



/-! ## The semiprime model -/

theorem ForkPinning.semiprime_OR_mutualInfo:
    mutualInfo cubicClassOfN splitOR
      = Real.log 3 - (5 / 9) * Real.log 5 - (2 / 9) * Real.log 2 := by sorry
