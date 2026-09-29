-- Prove2me | solution 1 for ForkPinning.semiprime_collapse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:13:41.809138+00:00
-- url     : https://prove2.me/submissions/b9089cee-0b09-4678-9920-72bce2dad387

-- Sol generated from Probability/ForkPinningSemiprime.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
import Theorems.Thm_ForkPinning_cyclicCubic_fork_mutualInfo
import Theorems.Thm_ForkPinning_semiprime_OR_mutualInfo
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

















/-! ## The which-factor wall -/





open ForkPinning in
theorem solution:
    12 * mutualInfo cubicClassOfN splitOR < mutualInfo (id : ZMod 3 → ZMod 3) forkC3 := by
  rw [semiprime_OR_mutualInfo, cyclicCubic_fork_mutualInfo]
  -- reduces to `3^33 < 2^6 · 5^20`
  have h1 : Real.log (5559060566555523) < Real.log (6103515625000000) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h2 : Real.log (5559060566555523) = 33 * Real.log 3 := by
    rw [show (5559060566555523 : ℝ) = 3 ^ 33 by norm_num, Real.log_pow]
    push_cast; ring
  have h3 : Real.log (6103515625000000) = 6 * Real.log 2 + 20 * Real.log 5 := by
    rw [show (6103515625000000 : ℝ) = 2 ^ 6 * 5 ^ 20 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [h2, h3] at h1
  linarith
