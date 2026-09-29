-- Prove2me | Definitions.Def_Logic_DifferentialGeometry_ProofMetric
-- name    : Logic_DifferentialGeometry_ProofMetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:01.353983+00:00
-- url     : https://prove2.me/theorems/d9a7d262-6a4f-4583-a873-787e2c77d8ef
-- title:
--   Aether Catalog definitions — Logic_DifferentialGeometry_ProofMetric
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DifferentialGeometry.ProofMetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DifferentialGeometry/ProofMetric.lean by skeleton subtraction
import Mathlib
/-
# Proof Phase Transitions IV: The Proof Metric and Graded Composition

This module **extends** the proof–phase–transition program of
`Logic.ProofPhaseTransitions` (the `ImplTheory`/`Derivable` package) and its length-graded
refinement `Logic.ImplicationalThreshold` (`DerivOfLen`, `minDerivLen`, the diameter
theorem `minDerivLen_chain`).  Those files supplied a length-graded derivability predicate
`DerivOfLen T a b k` ("there is a derivation of `b` from `a` using exactly `k` axiom
applications") and the *minimal* proof length `minDerivLen T a b := sInf {k | DerivOfLen …}`,
but stopped short of the single most important *algebraic* fact about proof length:
**it composes additively**.  This file supplies that missing engine and harvests its
consequences.

Headline results:

* `derivOfLen_comp` — **graded transitivity / additive composition**: a length-`m`
  derivation of `b` from `a` followed by a length-`n` derivation of `c` from `b` yields a
  length-`(m + n)` derivation of `c` from `a`.  This is the graded refinement of
  `ProofPhaseTransitions.derivable_trans`, and the structural heart of the whole file.
* `minDerivLen_self` — the minimal proof length of `a ⊢ a` is `0` (the reflexive base).
* `minDerivLen_triangle` — the **proof quasi-metric**: `minDerivLen` satisfies the directed
  triangle inequality `d(a,c) ≤ d(a,b) + d(b,c)` whenever both legs are derivable.  Together
  with `minDerivLen_self` this exhibits `minDerivLen T` as an (asymmetric, ℕ-valued)
  premetric on the atoms of any theory — the geometry underlying the proof-length program.
* `minDerivLen_chain_eq` — on the chain theory the metric is exactly the index gap:
  `minDerivLen chainT a b = b - a` for `a ≤ b` (sharpening the catalog diameter theorem
  `minDerivLen_chain`, the special case `a = 0`).
* `minDerivLen_chain_geodesic` — on the chain the triangle inequality is an **equality**
  for any ordered triple `a ≤ b ≤ c`: the chain realizes geodesics, with *no* proof slack.
* `loopLengths_add` — the **numerical-semigroup structure of loop lengths**: the set of
  lengths of closed derivations `a ⊢ a` contains `0` and is closed under addition, i.e. it
  is an additive submonoid of `ℕ`.  This is the cross-domain bridge from the proof-length
  program to numerical-semigroup / additive-combinatorics structure.

-- !-- Lab Notebook -- !--
-- Hypothesis: The length-graded layer `DerivOfLen` of the catalog should carry an *additive*
--   composition law mirroring `ReflTransGen.trans` but tracking lengths: concatenating an
--   `m`-step and an `n`-step derivation gives an `(m+n)`-step derivation.  If so, the minimal
--   proof length becomes a genuine ℕ-valued quasi-metric (reflexive + triangle inequality),
--   the chain becomes its geodesic (triangle is an equality), and loop lengths form an
--   additive submonoid of ℕ — connecting proof length to numerical-semigroup structure.
-- Result: All five pillars formalize.  `derivOfLen_comp` is a clean induction on the *second*
--   derivation (so the `+1`s accrue on the right, matching `m + (n+1) = (m+n)+1`).  The
--   triangle inequality combines `Nat.sInf_mem` on the two nonempty length sets with
--   `derivOfLen_comp` and `Nat.sInf_le`.  The chain metric is `b - a` because the length set
--   is the singleton `{b-a}` (by `chain_derivOfLen_iff`); the geodesic equality is then pure
--   `omega` from `a ≤ b ≤ c`.  Loop lengths inherit `0` (refl) and `+`-closure (comp).
-- Insight: Additive composability is what upgrades "derivability" (a *preorder*) to "proof
--   length" (a *metric geometry*).  The chain's geodesic rigidity (triangle = equality, length
--   set a singleton) is the extremal "zero-slack" case; random theories should instead show
--   strict triangle inequalities (shortcuts) and loop-length submonoids with nontrivial
--   Frobenius structure — the precise quantitative signature of a proof-length phase
--   transition.
-- Failure analysis: Inducting on the *first* derivation forces an awkward `(m+1)+n` regrouping;
--   inducting on the second keeps the arithmetic definitional.  `minDerivLen` on ℕ needs the
--   length set proven nonempty before `Nat.sInf_mem`/`Nat.sInf_le` apply; the chain singleton
--   identity needs `Set.mem_setOf_eq` unfolding before `omega`.
-- !-- end Lab Notebook -- !--
-/

open Relation

namespace ProofMetric

/-! ### Mirrored base infrastructure

The following declarations mirror `Logic.ProofPhaseTransitions` and
`Logic.ImplicationalThreshold` (`ImplTheory`, `Derivable`, `chainT`, `DerivOfLen`,
`minDerivLen`).  They are reproduced here so this file is self-contained; they are
*definitionally identical* to the catalog versions, so every result below extends the
catalog program on the very same objects. -/

/-- An **implicational theory** on atoms `α` (mirrors `ProofPhaseTransitions.ImplTheory`). -/
abbrev ImplTheory (α : Type*) := α → α → Prop


/-- The **chain theory** on `ℕ`: axioms `k → k+1` (mirrors `ProofPhaseTransitions.chainT`). -/
def chainT : ImplTheory ℕ := fun a b => b = a + 1

/-- **Length-graded derivability** (mirrors `ImplicationalThreshold.DerivOfLen`):
`DerivOfLen T a b k` asserts a derivation of `b` from `a` using *exactly* `k` axioms. -/
inductive DerivOfLen {α : Type*} (T : ImplTheory α) : α → α → ℕ → Prop
  | refl (a : α) : DerivOfLen T a a 0
  | tail {a b c : α} {n : ℕ} : DerivOfLen T a b n → T b c → DerivOfLen T a c (n + 1)

/-- The **minimal proof length** of `a ⊢ b` in `T` (mirrors
`ImplicationalThreshold.minDerivLen`). -/
noncomputable def minDerivLen {α : Type*} (T : ImplTheory α) (a b : α) : ℕ :=
  sInf {k | DerivOfLen T a b k}


/-! ### Graded composition: the engine -/

/-
!-- Graded transitivity: induct on the *second* derivation so the per-step `+1`s accrue on
the right (`m + (n+1) = (m+n)+1`), reapplying each axiom via `DerivOfLen.tail`. -- !--

**Graded transitivity / additive composition.** Concatenating a length-`m` derivation
of `b` from `a` with a length-`n` derivation of `c` from `b` yields a length-`(m + n)`
derivation of `c` from `a`. The length-tracking refinement of
`ProofPhaseTransitions.derivable_trans` and the structural engine of this file.
-/

/-! ### The proof quasi-metric -/

/-
!-- Reflexive base: `DerivOfLen.refl` puts `0` in the length set of `a ⊢ a`, and `0` is the
least natural number, so its infimum is `0`. -- !--

The minimal proof length of `a ⊢ a` is `0`.
-/

/-
!-- Triangle inequality: realize the two minimal lengths via `Nat.sInf_mem` on the nonempty
length sets, compose them with `derivOfLen_comp` into a length-`(m+n)` derivation `a ⊢ c`,
then bound the infimum from below with `Nat.sInf_le`. -- !--

**Proof quasi-metric (directed triangle inequality).** Whenever both legs are derivable,
`minDerivLen T a c ≤ minDerivLen T a b + minDerivLen T b c`. Together with
`minDerivLen_self` this exhibits `minDerivLen T` as a ℕ-valued premetric on atoms.
-/

/-! ### The chain is the geodesic: zero proof slack -/

/-
!-- The length set of `a ⊢ b` in the chain is the singleton `{b - a}` (by
`chain_derivOfLen_iff` and `a ≤ b`), whose infimum is `b - a`. -- !--

On the chain theory the proof metric is exactly the index gap:
`minDerivLen chainT a b = b - a` for `a ≤ b`. Sharpens the catalog diameter theorem
`ImplicationalThreshold.minDerivLen_chain` (the case `a = 0`).
-/

/-
!-- Geodesic equality: substitute `minDerivLen_chain_eq` on all three legs; the resulting
`c - a = (b - a) + (c - b)` is pure `omega` from `a ≤ b ≤ c`. -- !--

**Chain geodesic / zero slack.** On the chain theory the triangle inequality is an
*equality* for every ordered triple `a ≤ b ≤ c`: the chain realizes geodesics, with no
proof slack. This is the extremal minimal-density witness for the proof-length program.
-/

/-! ### Loop lengths form an additive submonoid -/

/-
!-- `0` is a loop length by `DerivOfLen.refl`; closure under `+` is `derivOfLen_comp`
with `b = c = a`. -- !--

**Numerical-semigroup structure of loop lengths.** The set of lengths of closed
derivations `a ⊢ a` contains `0` and is closed under addition: it is an additive submonoid
of `ℕ`. This bridges the proof-length program to numerical-semigroup structure.
-/


end ProofMetric


