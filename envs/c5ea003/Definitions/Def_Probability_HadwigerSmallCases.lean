-- Prove2me | Definitions.Def_Probability_HadwigerSmallCases
-- name    : Probability_HadwigerSmallCases
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:59.141369+00:00
-- url     : https://prove2.me/theorems/f9d47259-521b-46d4-b66e-def697511cfe
-- title:
--   Aether Catalog definitions — Probability_HadwigerSmallCases
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerSmallCases`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerSmallCases.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_HadwigerBipartite
import Definitions.Def_Probability_HadwigerK3
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

namespace Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Hadwiger's conjecture for the parameter `k`**: every finite graph that
cannot be properly coloured with `k` colours contains `K_{k+1}` as a minor. -/
def HadwigerProperty (k : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ G.Colorable k → CompleteMinor (k + 1) G








end Hadwiger


