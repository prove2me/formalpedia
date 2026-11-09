-- Prove2me | Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
-- name    : Couret_RecohCyclicHalves_383c4510168a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:48.891409+00:00
-- url     : https://prove2.me/theorems/efc3ac7f-637c-4a82-97c2-5e914a563b4a
-- title:
--   Partial solvers for doubling
-- statement:
--   A half solver is sound when returning $x$ implies $2x=t$, and complete when every solvable input receives some answer. For a cyclic modulus $q$, odd $q$ uses multiplication by $(q+1)/2$; even $q$ accepts exactly even canonical representatives and halves them. The product solver applies this coordinatewise. No uniqueness of the returned half is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicHalves.lean; source file SHA-256 a4e0211ade942e149c23077a732176c321236fab9e7cca6522d82ba445be71bd

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Coordinatewise doubling solver used by the exact RECOH decoder.

The cyclic solver uses the canonical natural representative of a ZMod value.
For odd modulus it multiplies by (q+1)/2; for even modulus it rejects an odd
representative and otherwise divides that representative by two.  The product
solver checks only the finitely many coordinates, never the ambient group.
This is Lean code with proved soundness and completeness, rather than a claim
that a separate Python parser, cache or runtime has been verified.
-/

namespace Couret.STROBO2TORS

/-- A sound and complete choice of one solution to a doubling equation. -/
def RecohHalfSolverSpec {G : Type*} [AddCommGroup G]
    (half : G → Option G) : Prop :=
  (∀ t x, half t = some x → x + x = t) ∧
  (∀ t, (∃ x, x + x = t) → ∃ x, half t = some x)

/-- Exactly the coordinate formula used by `CyclicProduct.half`. -/
def recohCyclicHalf (q : ℕ) (t : ZMod q) : Option (ZMod q) :=
  if q % 2 = 1 then some ((t.val * ((q + 1) / 2) : ℕ) : ZMod q)
  else if t.val % 2 = 0 then some ((t.val / 2 : ℕ) : ZMod q)
  else none

theorem recoh_odd_cyclic_half_double (q : ℕ) [NeZero q]
    (hq : q % 2 = 1) (t : ZMod q) :
    ((t.val * ((q + 1) / 2) : ℕ) : ZMod q) +
      ((t.val * ((q + 1) / 2) : ℕ) : ZMod q) = t := by
  have heven : (q + 1) / 2 + (q + 1) / 2 = q + 1 := by omega
  calc
    ((t.val * ((q + 1) / 2) : ℕ) : ZMod q) +
        ((t.val * ((q + 1) / 2) : ℕ) : ZMod q) =
        ((t.val * (((q + 1) / 2) + ((q + 1) / 2)) : ℕ) : ZMod q) := by
          push_cast
          ring
    _ = ((t.val * (q + 1) : ℕ) : ZMod q) := by rw [heven]
    _ = t := by simp

theorem recoh_even_value_half_double (q : ℕ) [NeZero q]
    (t : ZMod q) (ht : t.val % 2 = 0) :
    ((t.val / 2 : ℕ) : ZMod q) + ((t.val / 2 : ℕ) : ZMod q) = t := by
  have hval : t.val / 2 + t.val / 2 = t.val := by omega
  rw [← Nat.cast_add, hval]
  simp

theorem recoh_even_cyclic_double_value (q : ℕ) [NeZero q]
    (hq : q % 2 = 0) (x : ZMod q) : (x + x).val % 2 = 0 := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hq)]
  omega

theorem recoh_cyclic_half_sound (q : ℕ) [NeZero q]
    (t x : ZMod q) (hx : recohCyclicHalf q t = some x) : x + x = t := by
  unfold recohCyclicHalf at hx
  split_ifs at hx with hq ht
  · cases Option.some.inj hx
    exact recoh_odd_cyclic_half_double q hq t
  · cases Option.some.inj hx
    exact recoh_even_value_half_double q t ht

theorem recoh_cyclic_half_complete (q : ℕ) [NeZero q]
    (t : ZMod q) (ht : ∃ x, x + x = t) :
    ∃ x, recohCyclicHalf q t = some x := by
  by_cases hq : q % 2 = 1
  · exact ⟨((t.val * ((q + 1) / 2) : ℕ) : ZMod q),
      by simp [recohCyclicHalf, hq]⟩
  · have hq0 : q % 2 = 0 := by omega
    obtain ⟨x, rfl⟩ := ht
    exact ⟨(((x + x).val / 2 : ℕ) : ZMod q),
      by simp [recohCyclicHalf, hq, recoh_even_cyclic_double_value q hq0 x]⟩



/-- The product solver performs one cyclic calculation per coordinate. -/
def recohProductHalf {d : ℕ} (q : Fin d → ℕ)
    (t : (i : Fin d) → ZMod (q i)) : Option ((i : Fin d) → ZMod (q i)) :=
  if ∀ i, (recohCyclicHalf (q i) (t i)).isSome then
    some (fun i => (recohCyclicHalf (q i) (t i)).getD 0)
  else none

theorem recoh_product_half_sound {d : ℕ} (q : Fin d → ℕ)
    [∀ i, NeZero (q i)] (t x : (i : Fin d) → ZMod (q i))
    (hx : recohProductHalf q t = some x) : x + x = t := by
  unfold recohProductHalf at hx
  split_ifs at hx with h
  · cases Option.some.inj hx
    funext i
    have hi := h i
    cases he : recohCyclicHalf (q i) (t i) with
    | none => simp [he] at hi
    | some y =>
      simpa [he] using recoh_cyclic_half_sound (q i) (t i) y he

theorem recoh_product_half_complete {d : ℕ} (q : Fin d → ℕ)
    [∀ i, NeZero (q i)] (t : (i : Fin d) → ZMod (q i))
    (ht : ∃ x, x + x = t) : ∃ x, recohProductHalf q t = some x := by
  obtain ⟨x, hx⟩ := ht
  have h : ∀ i, (recohCyclicHalf (q i) (t i)).isSome := by
    intro i
    obtain ⟨y, hy⟩ := recoh_cyclic_half_complete (q i) (t i)
      ⟨x i, congrFun hx i⟩
    simp [hy]
  exact ⟨(fun i => (recohCyclicHalf (q i) (t i)).getD 0),
    by simp [recohProductHalf, h]⟩

theorem recoh_product_half_spec {d : ℕ} (q : Fin d → ℕ)
    [∀ i, NeZero (q i)] : RecohHalfSolverSpec (recohProductHalf q) :=
  ⟨recoh_product_half_sound q, recoh_product_half_complete q⟩

end Couret.STROBO2TORS


