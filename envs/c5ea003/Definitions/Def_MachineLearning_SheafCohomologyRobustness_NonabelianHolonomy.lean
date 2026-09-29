-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_NonabelianHolonomy
-- name    : MachineLearning_SheafCohomologyRobustness_NonabelianHolonomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:58:50.43509+00:00
-- url     : https://prove2.me/theorems/29fe51e7-0b2f-4993-8016-c7a5fbbc6f9a
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_NonabelianHolonomy
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.NonabelianHolonomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/NonabelianHolonomy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
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


namespace SheafCohomologyRobustness
namespace Nonabelian

open GraphNerve

variable {ι : Type*} {G : Type*} [Group G]

/-- Monodromy of a group-valued transition cochain along a walk: the ordered
product of the transitions crossed. -/
def wprod (c : ι → ι → G) : ι → List ι → G
  | _, [] => 1
  | i, j :: t => c i j * wprod c j t





/-- Trivial monodromy: the transition product around every closed walk is the
identity. -/
def TrivialMonodromy (A : ι → ι → Prop) (c : ι → ι → G) : Prop :=
  ∀ i l, IsWalk A i l → endpt i l = i → wprod c i l = 1

/-- `c` is a nonabelian coboundary: the transitions come from a single global
relabeling `f`. -/
def IsMulCoboundaryOn (A : ι → ι → Prop) (c : ι → ι → G) : Prop :=
  ∃ f : ι → G, ∀ i j, A i j → c i j = (f i)⁻¹ * f j







/-! ## §3. A realised three-class obstruction -/

/-- An explicit transition cochain for a three-class classifier on three mutually
overlapping regions: crossing an overlap "upwards" applies the transposition of
classes `0` and `1`, crossing it downwards applies its inverse. -/
def exTransition : Fin 3 → Fin 3 → Equiv.Perm (Fin 3) := fun x y =>
  if x.val < y.val then Equiv.swap 0 1 else if y.val < x.val then (Equiv.swap 0 1)⁻¹ else 1




end Nonabelian
end SheafCohomologyRobustness


