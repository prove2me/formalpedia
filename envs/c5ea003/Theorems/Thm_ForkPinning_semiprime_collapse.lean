-- Prove2me | Theorems.Thm_ForkPinning_semiprime_collapse
-- name    : ForkPinning.semiprime_collapse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:35.237282+00:00
-- url     : https://prove2.me/theorems/db665bae-8870-41cc-a5a5-7cd546b90f09
-- title:
--   The collapse.
-- statement:
--   **The collapse.**  Even a 100%-pinned prime-level fork degenerates at the semiprime level:
--   twelve times the semiprime information is still less than the prime-level information.
--
--   ```lean
--   theorem ForkPinning.semiprime_collapse:
--       12 * mutualInfo cubicClassOfN splitOR < mutualInfo (id : ZMod 3 → ZMod 3) forkC3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningSemiprime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningSemiprime.lean#L127

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

theorem ForkPinning.semiprime_collapse:
    12 * mutualInfo cubicClassOfN splitOR < mutualInfo (id : ZMod 3 → ZMod 3) forkC3 := by sorry
