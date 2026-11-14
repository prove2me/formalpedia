-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:25.192804+00:00
-- url     : https://prove2.me/theorems/fca37e9a-a12d-467d-b2ef-ee342f1d85fe
-- title:
--   Finite boxes, residue-class means, and quotient decompositions
-- statement:
--   For a finite coordinate type $\iota$ with decidable equality and natural side lengths $L_i$, the natural box is $\prod_i\{0,\ldots,L_i-1\}$ and the typed box is $\prod_i\mathrm{Fin}(L_i)$. A canonical equivalence identifies these representations. Box sums allow values in any additive commutative monoid; real box means divide the box sum by $\prod_iL_i$. The residue mean modulo $D$ is the mean on the constant-side box of length $D$.
--
--   Coordinatewise product splitting and quotient-remainder equivalences decompose a box of sides $q_iD$ into a quotient box and a residue box. Coordinatewise periodicity means constancy on vectors with equal residues modulo $D$. Trimming replaces each side $L$ by $\lfloor L/D\rfloor D$, with natural division giving zero when $D=0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CongruenceAverage.lean#L77-L400

import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/









/-! ## Finite boxes -/

/-- The natural-number box `∏ i, {0, ..., side i - 1}`. -/
def natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun i ↦ Finset.range (side i)

@[simp]
theorem mem_natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    {side : ι → ℕ} {x : ι → ℕ} :
    x ∈ natBox side ↔ ∀ i, x i < side i := by
  simp [natBox]



/-- A box represented as a finite type rather than a finset. -/
abbrev FiniteBox {ι : Type*} (side : ι → ℕ) :=
  ∀ i, Fin (side i)



/-- Sum a function on natural vectors over the box with the prescribed side
lengths. -/
def boxSum {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) : A :=
  ∑ x : FiniteBox side, F (fun i ↦ x i)

/-- The typed box is canonically equivalent to the subtype of points in the
literal natural-number box. -/
def finiteBoxEquivNatBox {ι : Type*}
    [Fintype ι] [DecidableEq ι] (side : ι → ℕ) :
    FiniteBox side ≃ ↥(natBox side) where
  toFun x := ⟨fun i ↦ x i, by simp⟩
  invFun x i := ⟨x.1 i, mem_natBox.mp x.2 i⟩
  left_inv x := by
    funext i
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    rfl



/-! ## Coordinatewise periodicity and exact box sums -/

/-- `F` is periodic modulo `D` in every coordinate, expressed in the form
most useful for congruence conditions: it is constant on coordinatewise
residue classes modulo `D`. -/
def PeriodicInEachCoordinate {ι A : Type*}
    (F : (ι → ℕ) → A) (D : ℕ) : Prop :=
  ∀ x y, (∀ i, x i % D = y i % D) → F x = F y















/-- Pointwise products split into a pair of pointwise functions. -/
def piProdEquiv {ι : Type*} {α β : ι → Type*} :
    (∀ i, α i × β i) ≃ ((∀ i, α i) × (∀ i, β i)) where
  toFun f := (fun i ↦ (f i).1, fun i ↦ (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinatewise quotient--remainder equivalence for a box with side
lengths `q i * D`.  The first component chooses a period block and the second
chooses the residue. -/
def boxQuotientEquiv {ι : Type*} (q : ι → ℕ) (D : ℕ) :
    (FiniteBox q × FiniteBox (fun _ : ι ↦ D)) ≃
      FiniteBox (fun i ↦ q i * D) :=
  piProdEquiv.symm.trans
    (Equiv.piCongrRight fun _ ↦ finProdFinEquiv)







/-! ## Exact means -/

/-- The uniform mean of a real-valued function on a natural box. -/
noncomputable def boxMean {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (F : (ι → ℕ) → ℝ) : ℝ :=
  boxSum side F / ∏ i, (side i : ℝ)

/-- The exact mean over coordinatewise residue classes modulo `D`. -/
noncomputable def meanMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (F : (ι → ℕ) → ℝ) : ℝ :=
  boxMean (fun _ : ι ↦ D) F





/-! ## Trimming and explicit boundary loss -/

/-- The largest multiple of `D` not exceeding `L`.  For `D = 0` this is
defined to be zero by natural-number division. -/
def trimToMultiple (D L : ℕ) : ℕ :=
  L / D * D













/-- Trim every side of a box to a multiple of `D`. -/
def trimmedSide {ι : Type*} (D : ℕ) (side : ι → ℕ) : ι → ℕ :=
  fun i ↦ trimToMultiple D (side i)















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.boxMean.eq_1,
    `Wikipedia.SzemeredisTheorem.boxSum.congr_simp,
    `Wikipedia.SzemeredisTheorem.boxSum.eq_1,
    `Wikipedia.SzemeredisTheorem.meanMod.eq_1,
    `Wikipedia.SzemeredisTheorem.natBox.eq_1,
    `Wikipedia.SzemeredisTheorem.trimToMultiple.eq_1,
    `Wikipedia.SzemeredisTheorem.trimmedSide.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


