-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.AffineForm.pairLinearMapZMod_surjective_of_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:11.69856+00:00
-- url     : https://prove2.me/submissions/bbadca0b-e440-4da6-bb29-75ef5af69837

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





@[simp]
theorem linearMapZMod_single {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (i : ι) (a : ZMod p) :
    ψ.linearMapZMod p (Pi.single i a) =
      (ψ.coefficient i : ZMod p) * a := by
  simp [linearMapZMod, Pi.single_apply, eq_comm]











@[simp]
theorem pairLinearMapZMod_apply {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    pairLinearMapZMod p ψ φ x =
      (ψ.linearMapZMod p x, φ.linearMapZMod p x) :=
  rfl



















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
/-- A nonzero two-by-two coefficient minor makes the pair of reduced linear
forms jointly surjective. -/
theorem solution
    {ι : Type*} [Fintype ι]
    {p : ℕ} [Fact p.Prime] (ψ φ : AffineForm ι ℤ)
    {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    Function.Surjective (pairLinearMapZMod p ψ φ) := by
  classical
  intro y
  have hij : i ≠ j := by
    intro hij
    subst j
    simp [coefficientMinor] at hdet
  let det : ZMod p :=
    (ψ.coefficient i : ZMod p) *
        (φ.coefficient j : ZMod p) -
      (ψ.coefficient j : ZMod p) *
        (φ.coefficient i : ZMod p)
  have hdet' : det ≠ 0 := by
    simpa [det, coefficientMinor] using hdet
  let u : ZMod p :=
    det⁻¹ *
      ((φ.coefficient j : ZMod p) * y.1 -
        (ψ.coefficient j : ZMod p) * y.2)
  let v : ZMod p :=
    det⁻¹ *
      (-(φ.coefficient i : ZMod p) * y.1 +
        (ψ.coefficient i : ZMod p) * y.2)
  let x : ι → ZMod p :=
    Pi.single i u + Pi.single j v
  refine ⟨x, ?_⟩
  apply Prod.ext
  · change ψ.linearMapZMod p x = y.1
    rw [show x = Pi.single i u + Pi.single j v by rfl,
      map_add, linearMapZMod_single, linearMapZMod_single]
    simp only [u, v]
    field_simp [hdet']
    simp only [det]
    ring
  · change φ.linearMapZMod p x = y.2
    rw [show x = Pi.single i u + Pi.single j v by rfl,
      map_add, linearMapZMod_single, linearMapZMod_single]
    simp only [u, v]
    field_simp [hdet']
    simp only [det]
    ring
