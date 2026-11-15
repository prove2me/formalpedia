-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.AffineForm.card_commonZeroFinsetZMod_mul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:03.7653+00:00
-- url     : https://prove2.me/submissions/edd587b0-83da-4a1b-ab00-99332b14741d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_pairLinearMapZMod_surjective_of_minor_ne_zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Elementary local densities of affine forms

This starts the local-factor calculation with the exact one-form density.
An integer affine form is reduced modulo `p`; if one coefficient remains
nonzero and `p` is prime, its linear part is surjective.  All fibers then
have the same cardinality, so the zero congruence occupies exactly a
`1 / p` fraction of the finite vector space (recorded first as an exact
natural-number identity).
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm







@[simp]
theorem evalZMod_eq_zero_iff {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    ψ.evalZMod p x = 0 ↔
      ψ.linearMapZMod p x = -(ψ.constant : ZMod p) := by
  simp [evalZMod, eq_neg_iff_add_eq_zero, add_comm]









@[simp]
theorem pairLinearMapZMod_apply {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    pairLinearMapZMod p ψ φ x =
      (ψ.linearMapZMod p x, φ.linearMapZMod p x) :=
  rfl





@[simp]
theorem mem_commonZeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ commonZeroFinsetZMod p ψ φ ↔
      ψ.evalZMod p x = 0 ∧ φ.evalZMod p x = 0 := by
  simp [commonZeroFinsetZMod]













end AffineForm





end Wikipedia.SzemeredisTheorem

end
/-!
# Elementary local densities of affine forms

This starts the local-factor calculation with the exact one-form density.
An integer affine form is reduced modulo `p`; if one coefficient remains
nonzero and `p` is prime, its linear part is surjective.  All fibers then
have the same cardinality, so the zero congruence occupies exactly a
`1 / p` fraction of the finite vector space (recorded first as an exact
natural-number identity).
-/
open Wikipedia.SzemeredisTheorem
open Wikipedia.SzemeredisTheorem.AffineForm

open Wikipedia.SzemeredisTheorem.AffineForm in
/-- Exact cardinal form of the codimension-two density of two independent
affine congruences. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    p ^ 2 * (commonZeroFinsetZMod p ψ φ).card =
      p ^ Fintype.card ι := by
  let : Fact p.Prime := ⟨hp⟩
  let L := pairLinearMapZMod p ψ φ
  have hsurj : Function.Surjective L :=
    pairLinearMapZMod_surjective_of_minor_ne_zero ψ φ hdet
  let target : ZMod p × ZMod p :=
    (-(ψ.constant : ZMod p), -(φ.constant : ZMod p))
  have hcommon :
      commonZeroFinsetZMod p ψ φ =
        Finset.univ.filter fun x : ι → ZMod p => L x = target := by
    ext x
    simp [L, target, evalZMod_eq_zero_iff]
  have hfiber (y : ZMod p × ZMod p) :
      ((Finset.univ.filter fun x : ι → ZMod p => L x = y).card) =
        (commonZeroFinsetZMod p ψ φ).card := by
    have h :=
      AddMonoidHom.card_fiber_eq_of_mem_range L.toAddMonoidHom
        (hsurj y) (hsurj target)
    rw [hcommon]
    change
      (Finset.univ.filter fun g : ι → ZMod p => L g = y).card =
        (Finset.univ.filter fun g : ι → ZMod p => L g = target).card
    exact h
  have hsplit :
      Fintype.card (ι → ZMod p) =
        ∑ y : ZMod p × ZMod p,
          (Finset.univ.filter fun x : ι → ZMod p =>
            L x = y).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (ι → ZMod p)))
        (t := (Finset.univ : Finset (ZMod p × ZMod p)))
        (f := fun x => L x)
        (fun _ _ => Finset.mem_univ _))
  rw [Fintype.card_fun, ZMod.card] at hsplit
  have hsplit' :
      p ^ Fintype.card ι =
        p ^ 2 * (commonZeroFinsetZMod p ψ φ).card := by
    calc
      p ^ Fintype.card ι =
          ∑ y : ZMod p × ZMod p,
            (Finset.univ.filter fun x : ι → ZMod p =>
              L x = y).card := hsplit
      _ = ∑ _y : ZMod p × ZMod p,
          (commonZeroFinsetZMod p ψ φ).card := by
        apply Finset.sum_congr rfl
        intro y _
        exact hfiber y
      _ = p ^ 2 * (commonZeroFinsetZMod p ψ φ).card := by
        simp [ZMod.card, pow_two]
  exact hsplit'.symm
