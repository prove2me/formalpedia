-- Prove2me | Definitions.Def_Bridges_UniversalComplexity_Core
-- name    : Bridges_UniversalComplexity_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:08.230487+00:00
-- url     : https://prove2.me/theorems/c9bdd5f4-abec-4d88-9e1c-0a29b806500f
-- title:
--   Aether Catalog definitions — Bridges_UniversalComplexity_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UniversalComplexity.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UniversalComplexity/Core.lean by skeleton subtraction
import Mathlib

/-!
# Universal Computational Complexity: Substrate-Independent Hierarchy Theory

We formalize the thesis that computational complexity hierarchies are universal
mathematical structures, independent of biological substrate or computational model.
Any civilization that discovers enumerable computation necessarily encounters
diagonal barriers, strict resource hierarchies, and simulation-transfer phenomena.

## Main Definitions

* `ResourceHierarchy` — Abstract monotone family of complexity classes
* `computationalDiag` — Diagonal construction for decision families
* `ModelSimulation` — Structure-preserving map between computation models
* `OracleAugmentation` — Oracle-enriched complexity hierarchy
* `HypercomputationalModel` — Model with transfinite oracle tower

## Main Results

* `computationalDiag_not_in_range` — Diagonal language escapes any enumeration
* `proper_hierarchy_strictMono` — Proper hierarchies yield infinite chains
* `simulation_comp_preserves` — Simulation composition transfers class containment
* `simulation_separation_transfer` — Strict separations transfer across models
* `oracle_diagonal_barrier` — Oracle augmentation cannot escape diagonalization
* `hypercomputation_hierarchy_exists` — Even transfinite hierarchies are strict
-/

noncomputable section
open Set Function

namespace UniversalComplexity

/-! ## Part I: The Computational Diagonal Argument

The foundation of ALL complexity hierarchy theorems is the diagonal argument.
We formalize it as a universal construction on ℕ-indexed families of sets,
showing that any enumerable computational model necessarily has undecidable
problems at each resource level. This is substrate-independent: it depends
only on countability of programs, not on the physics of computation. -/

/-- The computational diagonal set: given a family of languages (one per program),
    the diagonal language contains `n` exactly when program `n` does NOT accept `n`.
    This captures the essence of Turing's undecidability proof, the time hierarchy
    theorem, and Cantor's diagonal argument, unified in one construction. -/
def computationalDiag (family : ℕ → Set ℕ) : Set ℕ :=
  {n | n ∉ family n}

/-
**Computational Diagonal Theorem**: The diagonal language is never equal to
    any language in the enumeration. This single result implies that every
    computational model with ℕ-enumerable programs has problems outside any
    fixed resource class.

    This is the substrate-independent core of computational complexity:
    any civilization that discovers countable program enumeration MUST
    discover this separation.
-/

/-
The diagonal language disagrees with every member of the family on
    at least one input (namely, the program's own index).
-/

/-
The diagonal construction is functorial: composing with any injection
    preserves the diagonal property.
-/

/-! ## Part II: Resource Hierarchies

A `ResourceHierarchy` captures the order-theoretic structure common to
ALL complexity class hierarchies: TIME, SPACE, NONDETERMINISTIC-TIME,
circuit depth, quantum query complexity, etc. The key property is
monotonicity: more resources never decreases computational power.

We prove that proper (strict) hierarchies yield infinite ascending chains
in the powerset lattice, a structural theorem independent of any
computational model. -/

/-- A resource hierarchy: a monotone family of problem classes indexed by ℕ.
    This abstracts DTIME, DSPACE, NTIME, circuit complexity, etc. into
    a single order-theoretic framework. -/
structure ResourceHierarchy (α : Type*) where
  /-- The class of problems solvable at resource level `n` -/
  class_at : ℕ → Set α
  /-- Monotonicity: increasing resources never loses solvability -/
  mono : Monotone class_at

/-- A hierarchy is proper if each resource level strictly extends the previous.
    This is the abstract version of "P ⊊ EXP" or any time hierarchy theorem. -/
def ResourceHierarchy.IsProper {α : Type*} (H : ResourceHierarchy α) : Prop :=
  ∀ n, H.class_at n ⊂ H.class_at (n + 1)

/-
**Strict Monotonicity Theorem**: A proper hierarchy is strictly monotone
    as a function ℕ → Set α. This means not just adjacent levels differ,
    but ANY two distinct levels differ — there is genuinely an infinite chain
    of strictly increasing complexity classes.

    The proof requires induction over the gap between levels, using the
    proper hierarchy condition at each step.
-/

/-
In a proper hierarchy, every level witnesses a problem that requires
    exactly that level of resources.
-/

/-
A proper hierarchy over a type with at least one element has
    infinitely many distinct classes (no two levels are equal).
-/

/-! ## Part III: Model Simulation and Separation Transfer

A key thesis of universal complexity theory is that complexity separations
are model-independent (up to polynomial overhead). We formalize this via
`ModelSimulation`, a structure-preserving map between hierarchies that
respects resource bounds.

The main result: if two models can simulate each other with bounded
overhead, they have isomorphic hierarchy structures — and in particular,
strict separations in one model imply strict separations in the other. -/

/-- A simulation from hierarchy H₁ to H₂: an injective map that
    preserves membership in complexity classes up to bounded overhead. -/
structure ModelSimulation {α β : Type*}
    (H₁ : ResourceHierarchy α) (H₂ : ResourceHierarchy β) where
  /-- Embedding of problems from one model to another -/
  embed : α → β
  /-- Embedding preserves problem identity (injective) -/
  embed_inj : Injective embed
  /-- Resource overhead function -/
  overhead : ℕ → ℕ
  /-- Overhead is monotone -/
  overhead_mono : Monotone overhead
  /-- Problems solvable at level n in H₁ are solvable at level overhead(n) in H₂ -/
  preserves : ∀ n, embed '' (H₁.class_at n) ⊆ H₂.class_at (overhead n)

/-
**Simulation Composition**: Given simulations A → B and B → C,
    we get a simulation A → C with composed overhead. This shows that
    the simulation relation is transitive and overhead composes functorially.
-/

/-
**Separation Transfer Theorem**: An injective embedding preserves
    strict set containment. Therefore, if H₁ has a strict separation
    between levels m and n, this separation is preserved in the image
    under any injective simulation map.

    This formalizes the principle that "P vs NP is model-independent":
    any two models related by injective simulation must agree on
    which separations exist.
-/

/-! ## Part IV: Oracle Hierarchies and Diagonal Barriers

We show that even oracle-augmented computation models face diagonal
barriers. Adding an oracle to a computation model gives a new hierarchy,
but the diagonal argument applies equally well to the augmented model.

This formalizes the Baker-Gill-Solovay insight: relativization barriers
are universal, not an artifact of specific proof techniques. -/



/-
**Oracle Diagonal Barrier**: For any oracle-augmented model that
    still has ℕ-enumerable programs (as all physically realizable models do),
    the diagonal construction produces a language outside any fixed
    resource level of the oracle-augmented model.

    Formally: if the oracle-augmented languages are countably enumerated,
    the diagonal set is not among them.
-/

/-! ## Part V: Hypercomputational Barriers

Even hypercomputational models (those with access to oracles solving
the halting problem, or transfinite computation) face analogous
complexity barriers. We prove that the diagonal construction applies
at every level of a transfinite oracle tower. -/

/-- A hypercomputational model: a transfinite tower of increasingly
    powerful computation levels, each with its own enumerable programs. -/
structure HypercomputationalModel where
  /-- At each ordinal level, an enumeration of languages -/
  level_languages : ℕ → ℕ → Set ℕ
  /-- Each level includes all languages from lower levels -/
  level_cumulative : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
    range (level_languages k₁) ⊆ range (level_languages k₂)

/-
**Hypercomputation Hierarchy Theorem**: At every level of a
    hypercomputational tower, the diagonal construction yields
    a language not computable at that level.

    This proves that P-vs-NP-type barriers are not artifacts of
    Turing machine limitations: they arise from the mathematical
    structure of enumerable computation itself.
-/

/-
The hypercomputational hierarchy is properly cumulative under a
    mild assumption: each level's diagonal is computable at the next level.
-/

/-! ## Part VI: The Universality Principle

We formalize the key philosophical theorem: the structure of complexity
hierarchies is determined by three axioms alone:
1. Countable enumeration of programs
2. Monotonicity of resource bounds
3. Composability of simulations

Any system satisfying these axioms — whether silicon-based, biological,
quantum, or alien — necessarily exhibits the same hierarchy structure. -/

/-
A universal complexity principle: given any countable enumeration
    of decision procedures, the powerset of ℕ strictly exceeds what
    is enumerable. The number of problems is uncountable, but programs
    are countable — forcing a strict hierarchy of solvability.

    This counting argument is the deepest reason why complexity classes
    must form proper hierarchies.
-/

/-
Any two enumerations of languages have the same diagonal barrier:
    the diagonal set for one enumeration can be expressed via the
    diagonal set of a re-indexed enumeration.
-/

/-! ## Conjectures -/


end UniversalComplexity


