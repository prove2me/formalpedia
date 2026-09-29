-- Prove2me | solution 1 for Hadwiger.colorable_two_of_isAcyclic_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:32:39.801853+00:00
-- url     : https://prove2.me/submissions/f255dafd-e0f6-4f6f-a624-da7374f4cb26

-- Sol generated from Probability/HadwigerInfinite.lean
import Mathlib
import Definitions.Def_Probability_HadwigerInfinite
import Definitions.Def_Probability_HadwigerSmallCases
/-
  Hadwiger's Conjecture without Finiteness: the Cases k ≤ 2 for Arbitrary Graphs
  =============================================================================

  `HadwigerSmallCases.lean` proves Hadwiger's conjecture for `k ≤ 2` for finite
  graphs, the finiteness being used only in the colouring half
  (`colorable_two_of_isAcyclic`, an induction on the number of edges).  This
  file removes the hypothesis entirely: for `k ≤ 2` the conjecture holds for
  *every* vertex type, finite or not.

  The contraction half (`completeMinor_three_of_not_isAcyclic`, proved in
  `HadwigerK3.lean`) never needed finiteness; the colouring half is supplied in
  full generality by Mathlib's `SimpleGraph.IsAcyclic.isBipartite`, which
  two-colours an arbitrary forest by choosing a root in every connected
  component and using parity of distance to the root.

  Main results:

  * `Hadwiger.HadwigerPropertyGen`        : the conjecture with no finiteness
                                            assumption on the vertex type.
  * `Hadwiger.colorable_two_of_isAcyclic_general` : every forest, of any size,
                                            is 2-colourable.
  * `Hadwiger.hadwiger_gen_zero`, `hadwiger_gen_one`, `hadwiger_gen_two`
                                          : the general conjecture for k ≤ 2.
  * `Hadwiger.hadwigerProperty_of_gen`    : the general form implies the finite
                                            form, so these are genuine
                                            strengthenings.
  * `Hadwiger.colorable_two_of_no_K3_minor_general` : the excluded-minor form,
                                            valid for arbitrary graphs.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the finiteness hypothesis in the `k ≤ 2` cases is
    an artefact of the proof method (edge-count induction), not of the
    mathematics; the cases should survive verbatim for infinite graphs.
  Experiment (Experimenter): replaced the edge-count induction by the
    distance-parity colouring `SimpleGraph.IsAcyclic.isBipartite`
    (`IsBipartite` is by definition `Colorable 2`), which is stated in Mathlib
    for an arbitrary vertex type.  All three cases then go through with the
    `[Finite V]` binder deleted.
  Analysis (Analyst): the boundary of the phenomenon is `k = 3`.  For `k ≥ 3`
    even the *statement* becomes delicate for infinite graphs: `¬ Colorable k`
    for an infinite graph is, by de Bruijn–Erdős, equivalent to the existence of
    a finite non-`k`-colourable subgraph, so the general form for `k` follows
    from the finite form for `k` together with minor-monotonicity under
    subgraphs — a reduction that the low cases do not need.
  Critique (Critic): `hadwigerProperty_of_gen` is included precisely to certify
    that nothing was weakened: the general statement really does imply the
    finite one, so these are strengthenings and not incomparable variants.
  Synthesis (PI): the `k ≤ 2` fragment of Hadwiger's conjecture is a theorem
    about all graphs, and `colorable_two_iff_no_K3_minor` records it as a clean
    excluded-minor equivalence.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}









open Hadwiger in
theorem solution(h : G.IsAcyclic) : G.Colorable 2 :=
  h.isBipartite
