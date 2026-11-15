-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.AffineForm.card_zeroFinsetZMod_mul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:11.663233+00:00
-- url     : https://prove2.me/submissions/20a38f4a-b139-4f10-beeb-7768723285b5

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













/-- A nonzero coefficient makes the reduced linear form surjective over the
prime field. -/
theorem linearMapZMod_surjective_of_coefficient_ne_zero
    {ι : Type*} [Fintype ι]
    {p : ℕ} [Fact p.Prime] (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    Function.Surjective (ψ.linearMapZMod p) := by
  classical
  intro y
  let x : ι → ZMod p :=
    fun j =>
      if j = i then (ψ.coefficient i : ZMod p)⁻¹ * y else 0
  refine ⟨x, ?_⟩
  simp [linearMapZMod, x, hi]























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
/-- Exact cardinal form of the one-congruence local density. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    p * (ψ.zeroFinsetZMod p).card =
      p ^ Fintype.card ι := by
  let : Fact p.Prime := ⟨hp⟩
  let L := ψ.linearMapZMod p
  have hsurj : Function.Surjective L :=
    ψ.linearMapZMod_surjective_of_coefficient_ne_zero hi
  let target : ZMod p := -(ψ.constant : ZMod p)
  have hfiber (y : ZMod p) :
      ((Finset.univ.filter fun x : ι → ZMod p => L x = y).card) =
        (ψ.zeroFinsetZMod p).card := by
    have h :=
      AddMonoidHom.card_fiber_eq_of_mem_range L.toAddMonoidHom
        (hsurj y) (hsurj target)
    change
      (Finset.univ.filter fun g : ι → ZMod p => L g = y).card =
        (Finset.univ.filter fun g : ι → ZMod p => L g = target).card
    exact h
  have hsplit :
      Fintype.card (ι → ZMod p) =
        ∑ y : ZMod p,
          (Finset.univ.filter fun x : ι → ZMod p =>
            L x = y).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (ι → ZMod p)))
        (t := (Finset.univ : Finset (ZMod p)))
        (f := fun x => L x)
        (fun _ _ => Finset.mem_univ _))
  rw [Fintype.card_fun, ZMod.card] at hsplit
  have hsplit' :
      p ^ Fintype.card ι =
        p * (ψ.zeroFinsetZMod p).card := by
    calc
      p ^ Fintype.card ι =
          ∑ y : ZMod p,
            (Finset.univ.filter fun x : ι → ZMod p =>
              L x = y).card := hsplit
      _ = ∑ _y : ZMod p, (ψ.zeroFinsetZMod p).card := by
        apply Finset.sum_congr rfl
        intro y _
        exact hfiber y
      _ = p * (ψ.zeroFinsetZMod p).card := by
        simp [ZMod.card]
  exact hsplit'.symm
