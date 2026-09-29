-- Prove2me | Definitions.Def_Bridges_TropicalGodelKripkeReconstruction
-- name    : Bridges_TropicalGodelKripkeReconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:36:34.302202+00:00
-- url     : https://prove2.me/theorems/ef3ecc0a-708f-4098-849a-8b6c5af9035c
-- title:
--   Aether Catalog definitions — Bridges_TropicalGodelKripkeReconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalGodelKripkeReconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalGodelKripkeReconstruction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Gödel–Kripke Reconstruction: Idempotent Modal Semantics

This file establishes a formally verified bridge between tropical (min-plus) algebra and
modal logic semantics. The central results are:

1. **Tropical Modal Semantics**: Modal formulas are interpreted over finite weighted
   transition systems using min-plus algebra, where diamond is tropical matrix-vector
   multiplication and conjunction is pointwise minimum.

2. **Diamond–Inf Distributivity**: The tropical diamond operator distributes over
   pointwise minimum (conjunction), establishing that modal propagation is a tropical
   linear map on the semimodule of valuations.

3. **Tropical Hennessy–Milner Theorem**: Two states are modally indistinguishable up to
   depth `d` if and only if they agree on all tropical transfer profiles — the iterated
   diamond applications to atomic valuations.

4. **Modal Reconstruction**: Under a spectral separation hypothesis, the depth-`d` modal
   theory determines a canonical weighted quotient frame, reconstructible from finitely
   many tropical transfer samples.

## Mathematical Context

In the min-plus semiring (ℝ, min, +):
- **Tropical addition** is `min(a, b)`
- **Tropical multiplication** is `a + b`
- **Diamond operator**: `(◇_A v)(x) = inf_y (A(x,y) + v(y))`

The key insight is that `a + min(b, c) = min(a+b, a+c)` (tropical distributivity)
implies that diamond distributes over conjunction, making the modal transfer operator
a tropical linear map. This connects modal logic to tropical linear algebra and
weighted automata theory.

## References

- Gaubert, Katz: "The Minkowski theorem for max-plus convex sets"
- Hennessy, Milner: "Algebraic laws for nondeterminism and concurrency"
- Litvinov, Maslov: "Idempotent mathematics and mathematical physics"
-/

noncomputable section

open Finset BigOperators

namespace TropicalModal

/-! ## §1. Core Structures -/

/-- A **tropical Kripke frame** is a finite weighted transition system.
    The matrix `A x y` represents the weight (cost/distance) of transitioning
    from state `x` to state `y` in the min-plus semiring. -/
structure TropicalKripkeFrame (α : Type) [Fintype α] where
  /-- The tropical accessibility/transition weight matrix -/
  A : α → α → ℝ

/-- A **tropical valuation** assigns to each propositional variable a function
    from states to ℝ, representing the "cost" or "truth degree" of that
    proposition at each state in the min-plus semiring. -/
structure TropicalValuation (α : Type) (PropVar : Type) where
  /-- The valuation function: for each proposition and state, a real value -/
  val : PropVar → α → ℝ

/-- **Modal formulas** in the positive tropical fragment (without top/constants).
    - `atom p`: propositional variable
    - `conj φ ψ`: tropical conjunction (pointwise min)
    - `diamond φ`: tropical forward transfer (min-plus matrix action)

    This is the positive fragment where every formula evaluates to a pointwise
    minimum of iterated diamond applications to atomic valuations. -/
inductive ModalFormula (PropVar : Type) : Type
  | atom : PropVar → ModalFormula PropVar
  | conj : ModalFormula PropVar → ModalFormula PropVar → ModalFormula PropVar
  | diamond : ModalFormula PropVar → ModalFormula PropVar
  deriving Inhabited

/-! ## §2. Modal Depth -/

/-- The **modal depth** of a formula: the maximum nesting depth of diamond operators. -/
def ModalDepth {PropVar : Type} : ModalFormula PropVar → ℕ
  | .atom _ => 0
  | .conj φ ψ => max (ModalDepth φ) (ModalDepth ψ)
  | .diamond φ => ModalDepth φ + 1


/-! ## §3. Tropical Modal Evaluation -/

/-- The **tropical diamond operator**: forward transfer via min-plus matrix action.
    `(diamondEval F v)(x) = inf_y (F.A x y + v y)` -/
def diamondEval {α : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (v : α → ℝ) : α → ℝ :=
  fun x => Finset.univ.inf' Finset.univ_nonempty (fun y => F.A x y + v y)

/-- **Semantic evaluation** of modal formulas in the tropical Kripke semantics. -/
def evalModal {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar) :
    ModalFormula PropVar → α → ℝ
  | .atom p => V.val p
  | .conj φ ψ => fun x => min (evalModal F V φ x) (evalModal F V ψ x)
  | .diamond φ => diamondEval F (evalModal F V φ)

/-! ## §4. Key Algebraic Lemma: Inf-Min Distributivity -/

/-
**Finite inf distributes over min**: For finite nonempty types,
    `inf_y min(f y, g y) = min(inf_y f y, inf_y g y)`.
-/

/-! ## §5. Diamond–Inf Distributivity -/

/-
**Diamond distributes over conjunction**: `◇_A(min(v, w)) = min(◇_A(v), ◇_A(w))`
-/

/-! ## §6. Iterated Diamond -/

/-- **Iterated diamond**: `k`-fold application of the tropical diamond operator. -/
def iteratedDiamond {α : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) : ℕ → (α → ℝ) → (α → ℝ)
  | 0 => id
  | n + 1 => diamondEval F ∘ iteratedDiamond F n



/-! ## §7. Tropical Normal Forms

Every positive modal formula is semantically equivalent to a pointwise minimum of
iterated diamond applications to atomic valuations. This structural decomposition
is the key to the Hennessy-Milner theorem. -/

/-- A **tropical term** is a normal form for modal formulas:
    a tree of `min` nodes with `iteratedDiamond F k (V.val p)` at the leaves. -/
inductive TropicalTerm (PropVar : Type) : Type
  | single : ℕ → PropVar → TropicalTerm PropVar
  | minOf : TropicalTerm PropVar → TropicalTerm PropVar → TropicalTerm PropVar

/-- Evaluate a tropical term. -/
def evalTerm {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar) :
    TropicalTerm PropVar → α → ℝ
  | .single k p => iteratedDiamond F k (V.val p)
  | .minOf t1 t2 => fun z => min (evalTerm F V t1 z) (evalTerm F V t2 z)

/-- Maximum depth appearing in a tropical term. -/
def TropicalTerm.maxDepth {PropVar : Type} : TropicalTerm PropVar → ℕ
  | .single k _ => k
  | .minOf t1 t2 => max t1.maxDepth t2.maxDepth

/-- Shift a tropical term by incrementing all depths by 1. -/
def TropicalTerm.shift {PropVar : Type} : TropicalTerm PropVar → TropicalTerm PropVar
  | .single k p => .single (k + 1) p
  | .minOf t1 t2 => .minOf t1.shift t2.shift


/-
Evaluating a shifted term equals applying diamond to the original.
-/

/-
**Structural decomposition**: every positive modal formula has a tropical
    normal form — a min-tree of iterated diamond applications to atoms.
-/

/-
Tropical terms agree on spectrum-equivalent states.
-/

/-! ## §8. Tropical Spectral Equivalence -/

/-- Two states have the **same tropical spectrum up to depth d** if they agree
    on all transfer profiles `diamond^k(V(p))(x)` for all atoms `p` and `k ≤ d`. -/
def SameTropicalSpectrumUpToDepth
    {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar)
    (d : ℕ) (x y : α) : Prop :=
  ∀ (p : PropVar) (k : ℕ), k ≤ d →
    iteratedDiamond F k (V.val p) x = iteratedDiamond F k (V.val p) y





/-! ## §9. Spectral Separation -/

def SpectrallySeparated
    {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar)
    (d : ℕ) : Prop :=
  ∀ x y : α, SameTropicalSpectrumUpToDepth F V d x y → x = y

/-! ## §10. Tropical Hennessy–Milner Theorem -/


/-
**Backward**: Modal formula agreement → transfer profiles.
-/


/-! ## §11. Quotient Frame Construction -/


def WeightedBisimQuotientUpToDepth
    {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar)
    (d : ℕ) (Q : Type) [Fintype Q] [Nonempty Q]
    (_AQ : Q → Q → ℝ) (π : α → Q) : Prop :=
  Function.Surjective π ∧
  (∀ x y : α, π x = π y ↔ SameTropicalSpectrumUpToDepth F V d x y)

def CanonicallyReconstructedFromSamples
    {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar)
    (d : ℕ) (_Q : Type) [Fintype _Q] [Nonempty _Q]
    (_AQ : _Q → _Q → ℝ) (π : α → _Q) : Prop :=
  ∀ (p : PropVar) (k : ℕ), k ≤ d →
    ∀ x : α, iteratedDiamond F k (V.val p) x =
      iteratedDiamond F k (V.val p) (Function.invFun π (π x))

/-
**Tropical Modal Reconstruction Theorem**
-/

/-! ## §12. Diamond Properties -/




/-! ## §13. Tropical Closure Operator -/

def tropicalClosure {α : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (N : ℕ) (v : α → ℝ) : α → ℝ :=
  fun x => Finset.univ.inf' Finset.univ_nonempty
    (fun (k : Fin (N + 1)) => iteratedDiamond F k.val v x)



/-! ## §14. Reconstruction Certificate -/

structure ReconstructionCertificate (α : Type) [Fintype α] (d : ℕ) where
  correct_layers : Prop
  correct_quotient : Prop


end TropicalModal


