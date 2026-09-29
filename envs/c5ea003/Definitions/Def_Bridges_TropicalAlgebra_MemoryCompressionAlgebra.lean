-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_MemoryCompressionAlgebra
-- name    : Bridges_TropicalAlgebra_MemoryCompressionAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:00.493721+00:00
-- url     : https://prove2.me/theorems/018deee6-dfff-40eb-9fc3-c6324f91644c
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_MemoryCompressionAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.MemoryCompressionAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/MemoryCompressionAlgebra.lean by skeleton subtraction
import Mathlib
/-
# Memory Compression Algebra

A rigorous algebraic framework for memory-as-compression, connecting:
- Finite semigroup theory (idempotent stabilization)
- Tropical valuations (compression rank as tropical capacity)
- Information-theoretic bounds on composition

The central insight: information loss through memory has precise algebraic structure.
Every finite memory system eventually reaches an idempotent "steady state," and the
amount of information retained is governed by submultiplicative tropical inequalities.
-/


open Finset Function

/-! ## Part 1: Compression Rank and Submultiplicativity

The compression rank of a function f : α → β is |image(f)|.
For composed functions g ∘ f, we have |image(g ∘ f)| ≤ |image(f)|,
which captures that composition cannot increase information beyond
what the first stage passes through.
-/

noncomputable section

/-- The compression rank of a function on a finite type is the cardinality of its range. -/
def compressionRank {α : Type*} {β : Type*} (f : α → β) [Fintype α] [DecidableEq β] : ℕ :=
  (Finset.univ.image f).card

/-
**Image Monotonicity Under Composition**: composing with any function
cannot increase the compression rank beyond the inner function's rank.
This is the fundamental "information bottleneck" inequality.
-/

/-
Composition also cannot exceed the outer function's rank restricted to the image.
-/

/-
The compression rank of the identity function equals the cardinality of the type.
-/

/-! ## Part 2: Idempotent Stabilization in Finite Semigroups

Every element of a finite semigroup has an idempotent power: there exists n > 0
such that a^(2n) = a^n. This is the algebraic foundation of the "memory reaches
steady state" phenomenon.
-/

/-
In a finite monoid, every element has a power that is idempotent:
∃ n > 0, a^(2*n) = a^n. This captures that repeated application of any
memory transition eventually reaches a fixed point of the transition's effect.
-/

/-! ## Part 3: Tropical Capacity Valuation

The tropical capacity of a function is log(compressionRank(f)).
This valuation satisfies a tropical subadditivity law under composition:
  v(g ∘ f) ≤ min(v(f), v(g))
which is the max-plus dual of the bottleneck inequality.
-/

/-- Tropical capacity: the log of the compression rank.
Measures information capacity in nats. -/
def tropicalCapacity {α : Type*} {β : Type*} (f : α → β) [Fintype α] [DecidableEq β] : ℝ :=
  Real.log (compressionRank f : ℝ)

/-
**Tropical Bottleneck Inequality**: the tropical capacity of a composition
is at most the tropical capacity of the inner function.
In tropical terms: v(g ∘ f) ≤ v(f).
-/

/-! ## Part 4: Kernel Congruence and Information Ordering

The kernel of a function f : α → β defines an equivalence relation on α.
Coarser kernels mean more information loss.
We prove that if ker(f) refines ker(g), then the compression rank of g
is at most that of f — finer distinctions mean more information retained.
-/


/-- A function g factors through f if ker(f) refines ker(g):
whenever f(x) = f(y), also g(x) = g(y). -/
def KernelRefines {α : Type*} {β : Type*} {γ : Type*} (f : α → β) (g : α → γ) : Prop :=
  ∀ x y : α, f x = f y → g x = g y

/-
**Information Ordering Theorem**: If the kernel of f refines the kernel of g
(f makes finer distinctions), then g's compression rank is at most f's.
This formalizes "more information retained ⟹ at least as many distinct outputs."
-/

/-! ## Part 5: Memory System Structure -/

/-- A memory system consists of a finite state space with a
monoid action by an input alphabet via a monoid homomorphism. -/
structure MemorySystem (α : Type*) (S : Type*) [Monoid S] where
  /-- The transition function mapping input sequences to state transformations -/
  transition : FreeMonoid α →* S


/-- The cascade product of two memory systems creates a joint system
whose state space is the product S × T. -/
def cascadeProduct {α : Type*} {S : Type*} {T : Type*} [Monoid S] [Monoid T]
    (M₁ : MemorySystem α S) (M₂ : MemorySystem α T) :
    MemorySystem α (S × T) where
  transition := MonoidHom.prod M₁.transition M₂.transition

/-
**Cascade Product Rank Bound**: The compression rank of a cascade product
is at most the product of the individual compression ranks.
-/

/-! ## Part 6: Fixed Point Theorem for Memory Compression

The composition of compressionRank with iteration satisfies a monotone
convergence property: for any endofunction f on a finite type,
the sequence compressionRank(f^n) is non-increasing and eventually constant.
-/

/-
The compression rank sequence of iterates is non-increasing.
-/

/-
**Stabilization Theorem**: For any endofunction on a finite type,
the compression rank sequence eventually stabilizes.
-/

/-! ## Part 7: Surjection-Injection Factorization and Rank -/

/-
The compression rank of a surjective function equals the cardinality of the codomain.
-/

/-
The compression rank of an injective function equals the cardinality of the domain.
-/

end


