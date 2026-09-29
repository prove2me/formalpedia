-- Prove2me | Theorems.Thm_SheafCohomologyRobustness_Nonabelian_nonabelian_isCoboundary_of_trivial_monodromy
-- name    : SheafCohomologyRobustness.Nonabelian.nonabelian_isCoboundary_of_trivial_monodromy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:53:26.407905+00:00
-- url     : https://prove2.me/theorems/9193c4ee-bb4e-4525-9dcb-c0675aa6d3e2
-- title:
--   Sufficiency: the nonabelian discrete Poincaré lemma.
-- statement:
--   **Sufficiency: the nonabelian discrete Poincaré lemma.**  On a connected
--   nerve, a transition cochain whose monodromy is trivial around every closed walk
--   comes from a global relabeling.
--
--   ```lean
--   theorem SheafCohomologyRobustness.Nonabelian.nonabelian_isCoboundary_of_trivial_monodromy[Nonempty ι]
--       {A : ι → ι → Prop} {c : ι → ι → G}
--       (hsym : ∀ x y, A x y → A y x) (hinv : ∀ x y, c y x = (c x y)⁻¹)
--       (hconn : IsConnectedNerve A) (hmon : TrivialMonodromy A c) :
--       IsMulCoboundaryOn A c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/SheafCohomologyRobustness/NonabelianHolonomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/SheafCohomologyRobustness/NonabelianHolonomy.lean#L119

-- Thm stub generated from MachineLearning/SheafCohomologyRobustness/NonabelianHolonomy.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NonabelianHolonomy
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Nonabelian `H¹` of a Nerve: Multi-Class Decision Monodromy

For a binary classifier the decision sheaf takes values in `±1` and its
obstruction is the abelian class of `LoopCoefficients.parity_obstruction`.  For a
`k`-class classifier the local sections are *relabelings*, so the transition data
lives in a group that is **not** abelian, and the obstruction is a monodromy
representation rather than a sum.

This file proves the nonabelian discrete Poincaré lemma:

> On a connected nerve graph, a group-valued transition cochain `c` with
> `c j i = (c i j)⁻¹` is a coboundary (`c i j = (f i)⁻¹ * f j`) **iff** the
> product of transitions around every closed walk is the identity.

Main results.

* `wprod_revW` — reversing a walk inverts its holonomy (nonabelian analogue of
  `GraphNerve.wsum_revW`).
* `nonabelian_isCoboundary_of_trivial_monodromy`,
  `nonabelian_discrete_poincare` — the equivalence.
* `not_isCoboundary_of_monodromy_ne_one` — a single loop with nontrivial
  monodromy is a certificate that no global relabeling exists.
* `perm_monodromy_obstructs_global_labelling` — the multi-class specialisation:
  if transporting the predicted labels of a `k`-class classifier around a loop of
  overlapping regions permutes them nontrivially, no globally consistent labelling
  of the cover exists.  For `k = 2` this recovers the parity obstruction.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer, bold): binary robustness hides the nonabelian nature
  of the decision obstruction; for `k ≥ 3` classes, holonomies compose rather
  than add, and the vanishing condition is triviality of a homomorphism from the
  loop group of the nerve.
* Experiment (Experimenter): the abelian proof transports once sums become
  ordered products and the potential convention is fixed as `c i j = (f i)⁻¹ f j`
  (the opposite convention `f j (f i)⁻¹` also works but flips every telescoping
  step, and mixing the two was the source of the first failed attempt).
* Analysis (Analyst): the only structural input is that reversal inverts, which
  is the group-theoretic form of the alternating condition; commutativity is
  never used, so the abelian theorem was strictly weaker than necessary — "needed
  a different definition", not "false".
* Critique (Critic): the multi-class corollary is nonvacuous, since a
  transposition has order `2 ≠ 1`, and the statement is a strict non-existence
  claim about global labellings, witnessed by an explicit loop.
* Synthesis (PI): abelian coefficients measure *how much* certificates disagree;
  nonabelian coefficients measure *how* the class labels get permuted.
-/


open SheafCohomologyRobustness
open Nonabelian

open GraphNerve

variable {ι : Type*} {G : Type*} [Group G]

theorem SheafCohomologyRobustness.Nonabelian.nonabelian_isCoboundary_of_trivial_monodromy[Nonempty ι]
    {A : ι → ι → Prop} {c : ι → ι → G}
    (hsym : ∀ x y, A x y → A y x) (hinv : ∀ x y, c y x = (c x y)⁻¹)
    (hconn : IsConnectedNerve A) (hmon : TrivialMonodromy A c) :
    IsMulCoboundaryOn A c := by sorry
