-- Prove2me | Definitions.Def_Applications_MTamariConstellationGeneralM_GeneratingTreeIso
-- name    : Applications_MTamariConstellationGeneralM_GeneratingTreeIso
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:29.904282+00:00
-- url     : https://prove2.me/theorems/734cccca-793a-4f08-ab20-57922ab35490
-- title:
--   Aether Catalog definitions — Applications_MTamariConstellationGeneralM_GeneratingTreeIso
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.MTamariConstellationGeneralM.GeneratingTreeIso`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/MTamariConstellationGeneralM/GeneratingTreeIso.lean by skeleton subtraction
import Mathlib

/-!
# Generating-tree isomorphisms ⟹ refined equinumerosity (reusable engine)

This file develops a small, rigorous, reusable theory of **generating trees** and
their isomorphisms, in service of the research direction

*"Recursive decomposition isomorphism for general `m`-Tamari intervals and planar
`(m+1)`-constellations."*

A **generating tree** is a *root label* together with a *succession rule*
`succ : L → List L` giving the ordered list of labels of the children of a node.
Unfolding the rule level by level produces, at depth `k`, the ordered list of
labels of the nodes at that depth (`levelLabels`); the *counting sequence*
(`levelCount`) is the sequence of level sizes — in applications, the number of
objects of each size.

The core principle: two families with **isomorphic** generating trees (equal
succession rule up to a relabelling `φ` of labels) are equinumerous, and in fact
*equinumerous refined by every statistic carried by the labels*.  We prove:

* `GenTreeM.levelLabels_map`   — level-by-level correspondence through `φ`;
* `GenTreeM.levelCount_eq`     — the counting sequences coincide;
* `GenTreeM.refined_count_eq`  — refined counts coincide, level by level.

The concrete general-`m` succession rules and the isomorphism are developed in
`GeneralM.lean`, which proves the corresponding statements directly for the
concrete `m`-rules, mirroring this reusable engine.

-- !-- Lab Notes -- !--
HYPOTHESIS (framework).  "Isomorphism of generating trees" should be defined so it
*automatically* yields refined equinumerosity, without touching the combinatorial
objects.  The right datum is a label map `φ` intertwining the two succession rules
(`succ₂ ∘ φ = List.map φ ∘ succ₁`) and matching the roots (`φ root₁ = root₂`).

EXPERIMENT.  Define `levelLabels` by the two-line recursion (`level 0 = [root]`,
`level (k+1) = flatMap succ (level k)`).  The single non-trivial ingredient is the
interchange lemma `(xs.map φ).flatMap succ₂ = (xs.flatMap succ₁).map φ`, proved by
induction on `xs` from the intertwining hypothesis.  An induction on `k` then gives
`levelLabels succ₂ root₂ k = (levelLabels succ₁ root₁ k).map φ`.

ANALYSIS.  Everything downstream (equal counts, equal refined counts) follows by
`List.length_map` / `List.countP_map`.  The refined statement uses that statistics
`w₁, w₂` with `w₂ ∘ φ = w₁` have equal `countP` profiles.

CRITIQUE.  Non-vacuous: `levelLabels_map` is a genuine list identity proved by
nested induction, and `refined_count_eq` fails without the intertwining hypothesis
(a bare bijection of label *types* is insufficient).  No `rfl`/`native_decide`.

SYNTHESIS.  Reusable engine: to prove two families refined-equinumerous, exhibit a
label map intertwining their generating-tree succession rules.
-/

namespace GenTreeM

variable {L : Type*} {M : Type*}

/-- The ordered list of labels of the nodes at depth `k` of the generating tree
with succession rule `succ` and root `root`. -/
def levelLabels (succ : L → List L) (root : L) : ℕ → List L
  | 0 => [root]
  | k + 1 => (levelLabels succ root k).flatMap succ



/-- The number of nodes at depth `k`: the size-`k` term of the counting sequence. -/
def levelCount (succ : L → List L) (root : L) (k : ℕ) : ℕ :=
  (levelLabels succ root k).length





end GenTreeM


