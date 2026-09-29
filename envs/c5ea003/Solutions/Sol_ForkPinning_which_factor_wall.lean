-- Prove2me | solution 1 for ForkPinning.which_factor_wall
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:55.604719+00:00
-- url     : https://prove2.me/submissions/2da0e493-79d0-4923-b378-46e2313d0964

-- Sol generated from Probability/ForkPinningSemiprime.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
import Theorems.Thm_ForkPinning_mutualInfo_eq_zero_of_indep
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




lemma card_C3sq : Fintype.card (ZMod 3 × ZMod 3) = 9 := by decide

lemma prb_cubicClassOfN (k : ZMod 3) : prb cubicClassOfN k = 1 / 3 := by
  have h : ∀ k : ZMod 3, (fiber cubicClassOfN k).card = 3 := by decide
  rw [prb, card_C3sq, h k]
  norm_num












/-! ## The which-factor wall -/

lemma prb_firstFactorSplits_true : prb firstFactorSplits true = 1 / 3 := by
  rw [prb, card_C3sq, show (fiber firstFactorSplits true).card = 3 from by decide]
  norm_num

lemma prb_firstFactorSplits_false : prb firstFactorSplits false = 2 / 3 := by
  rw [prb, card_C3sq, show (fiber firstFactorSplits false).card = 6 from by decide]
  norm_num



open ForkPinning in
theorem solution: mutualInfo cubicClassOfN firstFactorSplits = 0 := by
  refine mutualInfo_eq_zero_of_indep _ _ (fun k b => ?_)
  have htrue : ∀ k : ZMod 3, (fiber (joint cubicClassOfN firstFactorSplits) (k, true)).card = 1 := by
    decide
  have hfalse : ∀ k : ZMod 3,
      (fiber (joint cubicClassOfN firstFactorSplits) (k, false)).card = 2 := by decide
  cases b with
  | false =>
      rw [prb, card_C3sq, hfalse k, prb_cubicClassOfN, prb_firstFactorSplits_false]
      norm_num
  | true =>
      rw [prb, card_C3sq, htrue k, prb_cubicClassOfN, prb_firstFactorSplits_true]
      norm_num
