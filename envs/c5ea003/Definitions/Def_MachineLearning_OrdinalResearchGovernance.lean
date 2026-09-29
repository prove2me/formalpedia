-- Prove2me | Definitions.Def_MachineLearning_OrdinalResearchGovernance
-- name    : MachineLearning_OrdinalResearchGovernance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:35.02262+00:00
-- url     : https://prove2.me/theorems/09fb1c36-cb8e-4dd4-bc53-734a671c2004
-- title:
--   Aether Catalog definitions — MachineLearning_OrdinalResearchGovernance
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.OrdinalResearchGovernance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/OrdinalResearchGovernance.lean by skeleton subtraction
import Mathlib
/-
# Ordinal Research Governance: Depth Guarantees via Proof-Theoretic Analysis

This module develops a formal theory of **ordinally certified automated discovery**,
where ordinal-valued depth functionals on research artifacts control non-triviality
and support automated triage of shallow cycles.

## Architecture

We define two complementary depth models:

1. **AetherOutput model**: A finite syntactic object with height, branching, novelty atoms,
   and dependencies. The ordinal depth is `height + branching`, giving a computable
   governance layer.

2. **ProofShape model**: An inductive type of proof constructors (axiom, compose, iterate,
   reflect) with genuinely transfinite ordinal depth via `ω`-exponentiation at reflection.
   This creates a phase transition between finitary and transfinite derivations.

## Main Results

* `depth_above_threshold_nontrivial` — Outputs above threshold ordinal are non-trivial.
* `innovationRank_le_ordinalDepth` — Innovation rank is dominated by ordinal depth.
* `cycleDepth_lt_iff_allBelow` — Cycle depth characterizes element-wise bounds.
* `shallow_cycle_rejected` — Shallow cycles have all outputs below threshold.
* `shallow_but_nontrivial_needs_escalation` — Mixed cycles require escalation.
* `psDepth_reflect_gt_finite` — Reflection strictly dominates finite iteration.
* `proofShape_nontrivial_of_depth_gt_one` — Deep proof shapes certify non-triviality.
* `reflectionFree_finite_depth` — Reflection-free shapes live below ω.
-/


open Ordinal Finset

/-! ## Part I: AetherOutput Model — Finite Syntactic Research Objects -/

/-- A finite syntactic object encoding a research output with structural metadata. -/
structure AetherOutput where
  size : Nat
  height : Nat
  branching : Nat
  noveltyAtoms : Finset Nat
  dependencies : Finset Nat
  deriving DecidableEq

/-- The shallow threshold ordinal: 2. -/
noncomputable def shallowThreshold : Ordinal := 2

/-- Ordinal depth of an AetherOutput: the sum of height and branching. -/
noncomputable def aetherDepth (x : AetherOutput) : Ordinal :=
  (x.height : Ordinal) + (x.branching : Ordinal)

/-- An output is shallow if both height and branching are at most 1. -/
def AetherShallow (x : AetherOutput) : Prop :=
  x.height ≤ 1 ∧ x.branching ≤ 1

/-- An output is research-nontrivial if it is not shallow. -/
def ResearchNontrivial (x : AetherOutput) : Prop :=
  ¬ AetherShallow x

instance : DecidablePred AetherShallow := fun x =>
  inferInstanceAs (Decidable (x.height ≤ 1 ∧ x.branching ≤ 1))

instance : DecidablePred ResearchNontrivial := fun x =>
  inferInstanceAs (Decidable (¬ AetherShallow x))

/-- Innovation rank: ordinal sum of novelty atom count and dependency count. -/
noncomputable def InnovationRank (x : AetherOutput) : Ordinal :=
  (x.noveltyAtoms.card : Ordinal) + (x.dependencies.card : Ordinal)

/-! ### Theorem 1: Threshold Depth Implies Non-Triviality -/

/-
Shallow outputs have ordinal depth at most 2.
-/

/-
**Theorem 1**: If an output's ordinal depth exceeds the shallow threshold,
    then it is research-nontrivial.
-/

/-
**Theorem 1 (Abstract)**: For any threshold τ, if all trivial outputs
    have depth ≤ τ, then any output with depth > τ is non-trivial.
    This is the abstract form: the threshold separates trivial from non-trivial.
-/

/-! ### Theorem 2: Innovation Bounded by Depth -/

/-
Innovation rank is bounded by ordinal depth when counts are bounded
    by height and branching respectively.
-/

/-! ## Part II: Research Cycles and Governance Policy -/

/-- A research cycle is a finite collection of AetherOutputs. -/
structure ResearchCycle where
  outputs : Finset AetherOutput

/-- The depth of a research cycle: supremum of output depths. -/
noncomputable def cycleDepth (C : ResearchCycle) : Ordinal :=
  C.outputs.sup aetherDepth

/-- All outputs in a cycle are below threshold τ. -/
def AllBelow (τ : Ordinal) (C : ResearchCycle) : Prop :=
  ∀ x ∈ C.outputs, aetherDepth x < τ


/-- A cycle needs escalation if it is shallow but contains non-trivial outputs. -/
def NeedsEscalation (τ : Ordinal) (C : ResearchCycle) : Prop :=
  cycleDepth C < τ ∧ ∃ x ∈ C.outputs, ResearchNontrivial x

/-! ### Theorem 3: Cycle Depth Characterization -/

/-
**Theorem 3**: Cycle depth below threshold iff all outputs below threshold.
    Requires the threshold to be positive (since `Finset.sup` of empty set is ⊥ = 0).
-/

/-
Shallow cycles have all outputs below threshold.
-/

/-! ### Theorem 4: Escalation Policy -/

/-
**Theorem 4**: A shallow cycle with a non-trivial output needs escalation.
-/

/-
**Policy Completeness**: Every shallow cycle is either purely trivial or needs escalation.
-/

/-! ## Part III: ProofShape Model — Transfinite Depth Semantics -/

/-- Proof shapes with constructors of increasing structural complexity.
    `reflect` introduces transfinite depth via ω-exponentiation. -/
inductive ProofShape : Type
  | axm : ProofShape
  | compose : ProofShape → ProofShape → ProofShape
  | iterate : Nat → ProofShape → ProofShape
  | reflect : ProofShape → ProofShape
  deriving DecidableEq

namespace ProofShape

/-- Ordinal-valued depth of a proof shape.
    Reflection applies ω-exponentiation, creating a phase transition. -/
noncomputable def psDepth : ProofShape → Ordinal
  | .axm => 0
  | .compose a b => Order.succ (max a.psDepth b.psDepth)
  | .iterate n a => a.psDepth + (n : Ordinal)
  | .reflect a => omega0 ^ a.psDepth

/-- Predicate: a proof shape contains a reflect constructor. -/
def hasReflect : ProofShape → Prop
  | .axm => False
  | .compose a b => hasReflect a ∨ hasReflect b
  | .iterate _ a => hasReflect a
  | .reflect _ => True


/-
Composition strictly increases depth (left component).
-/

/-
Composition strictly increases depth (right component).
-/

/-
**Key Theorem**: Reflection of a shape with positive depth produces depth ≥ ω,
    which exceeds any finite ordinal. This is the phase transition.
-/

/-
Reflection of a non-trivial shape has depth ≥ ω.
-/


/-
Reflection-free proof shapes have finite (< ω) depth.
-/

/-
Reflect constructor always produces positive depth.
-/

end ProofShape

/-! ## Part IV: Bridge Theorems -/

/-
Bridge theorem: Finset.sup characterization for ordinal depth.
-/

/-
Monotonicity: adding branching increases depth.
-/

/-
Monotonicity: adding height increases depth.
-/

/-! ## Part V: Decidable Governance -/

/-- Computable threshold check. -/
def aboveNatThreshold (n : Nat) (x : AetherOutput) : Bool :=
  n < x.height + x.branching

/-
The boolean decision agrees with the ordinal predicate.
-/

/-! ## Part VI: Depth Strict Monotonicity -/


