-- Prove2me | solution 1 for Hadwiger.completeMinor_three_C6
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:35:38.094716+00:00
-- url     : https://prove2.me/submissions/9d1fd6c8-dbfb-4fe2-a00d-6a7bec3b0373

-- Sol generated from Probability/HadwigerConverse.lean
import Mathlib
import Definitions.Def_Probability_HadwigerConverse
import Definitions.Def_Probability_HadwigerK3
import Theorems.Thm_Hadwiger_completeMinor_three_of_triple
import Theorems.Thm_Hadwiger_setConnected_pair
/-
  The Converse of Hadwiger's Conjecture is False
  ==============================================

  Hadwiger's conjecture says `χ(G) ≥ k+1 ⟹ K_{k+1} ≼ G`.  A natural — and
  frequently conjectured — strengthening is that the two conditions are
  *equivalent*, i.e. that the chromatic number is **minor-monotone**:
  `H ≼ G ⟹ χ(H) ≤ χ(G)`.  This file refutes that with an explicit
  counterexample: the `6`-cycle is bipartite yet contracts onto a triangle.

  Main results:

  * `Hadwiger.C6_colorable_two`            : `C₆` is `2`-colourable.
  * `Hadwiger.completeMinor_three_C6`      : `K₃` is a minor of `C₆`
                                             (branch sets `{0,1}, {2,3}, {4,5}`).
  * `Hadwiger.chromaticNumber_not_minorMonotone` : the chromatic number is **not**
                                             minor-monotone.
  * `Hadwiger.converse_hadwiger_false`     : consequently the converse of
                                             Hadwiger's implication fails for
                                             `k = 2` (and hence the conjecture
                                             cannot be upgraded to an
                                             equivalence).

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): contraction can *raise* the chromatic number, so
    the Hadwiger implication is strictly one-directional.
  Experiment (Experimenter): the smallest witness is the `6`-cycle: pairing up
    consecutive vertices `{0,1}, {2,3}, {4,5}` gives three connected, pairwise
    disjoint sets joined by the edges `1–2`, `3–4`, `5–0`, hence a `K₃` model,
    while the parity colouring shows `χ(C₆) = 2`.
  Analysis (Analyst): the phenomenon is exactly the failure of *odd* structure to
    be preserved under contraction — a bipartite graph can contract onto an odd
    cycle whenever it contains a cycle of length `≥ 4`.
  Critique (Critic): the witness must be checked to really be `C₆`
    (`SimpleGraph.cycleGraph 6`) and the colouring must be verified on all `36`
    ordered pairs; both are done by `decide` inside the proofs, but the
    surrounding statements are non-trivial mathematical claims.
  Synthesis (PI): Hadwiger's conjecture is an implication, never an equivalence;
    minor-closed classes therefore give upper bounds on `χ` only through the
    *excluded* minor, never through a contracted witness.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph







open Hadwiger in
theorem solution: CompleteMinor 3 C6 := by
  have a01 : C6.Adj 0 1 := by decide
  have a23 : C6.Adj 2 3 := by decide
  have a45 : C6.Adj 4 5 := by decide
  have a12 : C6.Adj 1 2 := by decide
  have a34 : C6.Adj 3 4 := by decide
  have a50 : C6.Adj 5 0 := by decide
  refine completeMinor_three_of_triple (S0 := {0, 1}) (S1 := {2, 3}) (S2 := {4, 5})
    ⟨0, by simp⟩ ⟨2, by simp⟩ ⟨4, by simp⟩ ?_ ?_ ?_
    (setConnected_pair a01) (setConnected_pair a23) (setConnected_pair a45)
    ⟨1, by simp, 2, by simp, a12⟩ ⟨0, by simp, 5, by simp, a50.symm⟩
    ⟨3, by simp, 4, by simp, a34⟩ <;>
  · rw [Set.disjoint_left]
    rintro a (rfl | rfl) <;> simp
