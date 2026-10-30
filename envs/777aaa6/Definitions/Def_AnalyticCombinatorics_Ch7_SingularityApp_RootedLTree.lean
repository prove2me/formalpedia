-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RootedLTree
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_RootedLTree
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T20:22:27.20368+00:00
-- url     : https://prove2.me/theorems/cd5f40db-631f-4ad6-9b11-fe0014519f8a
-- title:
--   Cayley counts for a recursive labelled rooted-tree species
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   inductive RootedLTree : ℕ → Type
--     | node {n : ℕ}
--         (r : Fin n)
--         (P : Finpartition (Finset.univ : Finset {x : Fin n // x ≠ r}))
--         (child : ∀ B : P.parts, RootedLTree B.val.card) :
--         RootedLTree n
--   ```
--
--   ```lean
--   def rootedLTreeClass : CombClass where
--     Obj n := RootedLTree n
--     finObj n := instFintypeRootedLTree n
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/RootedLTree.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Mathlib
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Rooted labelled trees as a recursive species, and Cayley's formula via Lagrange

We define a genuine recursive *rooted labelled tree* species object

  `RootedLTree n = root label + SET(rooted subtrees on a partition of the rest)`

and show its EGF satisfies `T = X · exp(T)`. By `implicitSeries_unique` and the
banked Lagrange coefficient `coeff_implicitSeries_exp`, the count is `n^{n-1}`,
matching the banked `cayleyRootedTree` (for `0 < n`).

This is the faithful species route to Cayley's coefficient — no Prüfer code.
-/

noncomputable section

open AnalyticCombinatorics.Ch1
open PowerSeries
open scoped BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS

/-- A labelled rooted tree on `n` labels, in recursive species form: a root
label plus a labelled SET of rooted subtrees on the remaining labels. -/
inductive RootedLTree : ℕ → Type
  | node {n : ℕ}
      (r : Fin n)
      (P : Finpartition (Finset.univ : Finset {x : Fin n // x ≠ r}))
      (child : ∀ B : P.parts, RootedLTree B.val.card) :
      RootedLTree n

/-! ## The recursive Fintype (the one real engineering lemma) -/

/-- `RootedLTree 0` is empty: there is no root in `Fin 0`. -/
def rootedLTreeZeroEquiv : RootedLTree 0 ≃ Empty where
  toFun t := by cases t with | node r P child => exact Fin.elim0 r
  invFun e := e.elim
  left_inv t := by cases t with | node r P child => exact Fin.elim0 r
  right_inv e := e.elim

/-- One-constructor decomposition equivalence for the successor case. -/
def rootedLTreeSuccEquiv (n : ℕ) :
    RootedLTree (n + 1) ≃
      Σ r : Fin (n + 1),
        Σ P : Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
          ∀ B : P.parts, RootedLTree B.val.card where
  toFun t := by cases t with | node r P child => exact ⟨r, P, child⟩
  invFun x := RootedLTree.node x.1 x.2.1 x.2.2
  left_inv t := by cases t with | node r P child => rfl
  right_inv x := by rcases x with ⟨r, P, child⟩; rfl

/-- Cardinality of the complement of one point in `Fin (n+1)`. -/
lemma fin_compl_ne_card (n : ℕ) (r : Fin (n + 1)) :
    Fintype.card {x : Fin (n + 1) // x ≠ r} = n := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter (fun x => x ≠ r) : Finset (Fin (n + 1)))
        = Finset.univ.erase r := by
    ext x; by_cases hx : x = r <;> simp [hx]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ r)]
  simp

/-- Each block of a partition of the (size-`n`) complement has `< n+1` elements. -/
lemma rootedLTree_part_card_lt
    {n : ℕ} {r : Fin (n + 1)}
    (P : Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}))
    (B : P.parts) :
    B.val.card < n + 1 := by
  have hle : B.val.card ≤ Fintype.card {x : Fin (n + 1) // x ≠ r} :=
    B.val.card_le_univ
  rw [fin_compl_ne_card n r] at hle
  exact Nat.lt_succ_of_le hle

/-- The recursive `Fintype`: well-founded recursion on `n`, building the Fintype
of the constructor argument Σ-type from recursive calls on strictly smaller
blocks (`B.val.card < n+1`). -/
instance instFintypeRootedLTree : (n : ℕ) → Fintype (RootedLTree n)
  | 0 => Fintype.ofEquiv Empty rootedLTreeZeroEquiv.symm
  | n + 1 => by
      classical
      haveI :
          ∀ r : Fin (n + 1),
            Fintype
              (Σ P : Finpartition
                (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
                ∀ B : P.parts, RootedLTree B.val.card) := by
        intro r
        haveI :
            ∀ P : Finpartition
              (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
              Fintype (∀ B : P.parts, RootedLTree B.val.card) := by
          intro P
          haveI : ∀ B : P.parts, Fintype (RootedLTree B.val.card) := by
            intro B
            have : B.val.card < n + 1 := rootedLTree_part_card_lt P B
            exact instFintypeRootedLTree B.val.card
          infer_instance
        infer_instance
      exact
        Fintype.ofEquiv
          (Σ r : Fin (n + 1),
            Σ P : Finpartition
              (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
              ∀ B : P.parts, RootedLTree B.val.card)
          (rootedLTreeSuccEquiv n).symm
  termination_by n => n
  decreasing_by exact this

/-! ## The species class and its functional equation -/

/-- The combinatorial class of rooted labelled trees. -/
def rootedLTreeClass : CombClass where
  Obj n := RootedLTree n
  finObj n := instFintypeRootedLTree n

@[simp] lemma rootedLTreeClass_counts (n : ℕ) :
    rootedLTreeClass.counts n = Fintype.card (RootedLTree n) := rfl

/-- Decomposition: a rooted tree on `n+1` labels is a root together with a
labelled SET of `rootedLTreeClass`-structures on the `n` remaining labels. -/
def decompEquiv (n : ℕ) :
    RootedLTree (n + 1) ≃
      Σ r : Fin (n + 1), labelledSetObj rootedLTreeClass {x : Fin (n + 1) // x ≠ r} :=
  rootedLTreeSuccEquiv n

/-! ## Cayley's coefficient via Lagrange inversion -/

/-! ## Connection to the banked Ch7 `cayleyRootedTree` / `treeFunctionCoeff` -/

end AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS


