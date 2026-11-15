-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_boxSum_sub_trimmed_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:34.991463+00:00
-- url     : https://prove2.me/submissions/6f1a1a4d-9918-4e55-a5bd-248f1aa58625

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section







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















/-- `boxSum` is the usual sum over the literal finset `natBox`. -/
theorem boxSum_eq_sum_natBox {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) :
    boxSum side F = ∑ x ∈ natBox side, F x := by
  rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (finiteBoxEquivNatBox side)
    (fun x : FiniteBox side ↦ F (fun i ↦ x i))
    (fun x : ↥(natBox side) ↦ F x)
    (fun _ ↦ rfl)

/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/





/-- Trimming never increases an interval. -/
theorem trimToMultiple_le (D L : ℕ) :
    trimToMultiple D L ≤ L :=
  Nat.div_mul_le_self L D











theorem trimmedSide_le {ι : Type*}
    (D : ℕ) (side : ι → ℕ) (i : ι) :
    trimmedSide D side i ≤ side i :=
  trimToMultiple_le D (side i)

/-- The coordinatewise trimmed box is contained in the original box. -/
theorem natBox_trimmed_subset {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D : ℕ) (side : ι → ℕ) :
    natBox (trimmedSide D side) ⊆ natBox side := by
  intro x hx
  rw [mem_natBox] at hx ⊢
  intro i
  exact (hx i).trans_le (trimmedSide_le D side i)











end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## LCM bounds -/
/-! ## Finite boxes -/
/-! ## Coordinatewise periodicity and exact box sums -/
/-! ## Exact means -/
/-! ## Trimming and explicit boundary loss -/

open Wikipedia.SzemeredisTheorem in
/-- Removing the boundary changes the sum of a bounded real function by at
most the boundary cardinality times the pointwise bound. -/
theorem solution {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F - boxSum (trimmedSide D side) F| ≤
      ((natBox side \ natBox (trimmedSide D side)).card : ℝ) * B := by
  rw [boxSum_eq_sum_natBox, boxSum_eq_sum_natBox,
    ← Finset.sum_sdiff_eq_sub (natBox_trimmed_subset D side)]
  calc
    |∑ x ∈ natBox side \ natBox (trimmedSide D side), F x| ≤
        ∑ x ∈ natBox side \ natBox (trimmedSide D side), |F x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ natBox side \ natBox (trimmedSide D side), B := by
      apply Finset.sum_le_sum
      intro x hx
      exact hF x (Finset.sdiff_subset hx)
    _ = ((natBox side \ natBox (trimmedSide D side)).card : ℝ) * B := by
      simp [nsmul_eq_mul]
