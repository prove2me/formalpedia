-- Prove2me | solution 1 for Hadwiger.hadwiger_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:39:57.825396+00:00
-- url     : https://prove2.me/submissions/bf8de247-64ae-4b45-92c0-5e107b840a81

-- Sol generated from Probability/HadwigerSmallCases.lean
import Mathlib
import Definitions.Def_Probability_HadwigerBipartite
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_HadwigerSmallCases
import Theorems.Thm_Hadwiger_colorable_two_of_isAcyclic
import Theorems.Thm_Hadwiger_completeMinor_three_of_not_isAcyclic
/-
  Hadwiger's Conjecture: Statement and the Cases k ≤ 2
  ===================================================

  Hadwiger's conjecture states that a graph whose proper colourings all need at
  least `k+1` colours contains `K_{k+1}` as a minor.  This file gives the formal
  statement `Hadwiger.HadwigerProperty k` in terms of the branch-set minor
  relation of `MinorModel.lean`, links it to Mathlib's `chromaticNumber`, and
  proves the conjecture unconditionally for `k = 0, 1, 2`.

  Main results:

  * `Hadwiger.HadwigerProperty`          : the formal statement.
  * `Hadwiger.not_colorable_iff_chromaticNumber_ge` : `¬ G.Colorable k` really
                                           says "needs at least `k+1` colours".
  * `Hadwiger.hadwiger_zero`, `Hadwiger.hadwiger_one`, `Hadwiger.hadwiger_two`
                                         : the conjecture for `k = 0, 1, 2`.
  * `Hadwiger.hadwiger_two_chromatic`    : the `k = 2` case in chromatic-number
                                           form: `3 ≤ χ(G) → K₃ ≼ G`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the low cases should follow from three separate
    structural facts — `χ ≥ 1 ⇒ a vertex`, `χ ≥ 2 ⇒ an edge`, `χ ≥ 3 ⇒ a cycle` —
    each converted into a branch-set model by the constructions of
    `HadwigerK3.lean`.
  Experiment (Experimenter): `k = 0` is `colorable_zero_iff`; `k = 1` needs "no
    edges ⇒ 1-colourable"; `k = 2` is the contrapositive of
    `colorable_two_of_isAcyclic` followed by `completeMinor_three_of_not_isAcyclic`.
  Analysis (Analyst): the three cases are genuinely different in strength: the
    `k = 2` case already needs both halves (colouring and contraction), which is
    the pattern that persists for `k = 3` (Dirac) and `k = 4` (Wagner + 4CT).
  Critique (Critic): the statement quantifies over finite vertex types in
    `Type`; the finiteness hypothesis is used only through the colouring half
    (`colorable_two_of_isAcyclic`), whose induction is on the edge count.
  Synthesis (PI): `k ≤ 2` is now a theorem of this development, and the
    remaining cases are isolated as explicit conditional statements in
    `HadwigerWagner.lean`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}










open Hadwiger in
theorem solution: HadwigerProperty 2 := by
  intro V _ G h
  have hacyc : ¬ G.IsAcyclic := fun hac => h (colorable_two_of_isAcyclic hac)
  exact completeMinor_three_of_not_isAcyclic hacyc
