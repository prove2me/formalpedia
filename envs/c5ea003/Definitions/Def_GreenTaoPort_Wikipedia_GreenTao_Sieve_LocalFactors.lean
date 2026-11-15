-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:53:53.746347+00:00
-- url     : https://prove2.me/theorems/eb378185-7116-4007-b3c6-7c058a6d4592
-- title:
--   Affine congruence maps and finite common-zero sets
-- statement:
--   An integer affine form on a finite variable type gives a linear map over $\mathbb Z/p\mathbb Z$ by reducing its coefficient vector modulo $p$. Adding its reduced constant gives the affine evaluation. A pair of forms gives the corresponding two-output linear map.
--
--   For a positive modulus $p$, the bundle also defines finite sets of solutions to one affine congruence and to a pair of simultaneous affine congruences. The single-form set is written as the fiber of the linear part over the negative constant; the pair set requires both affine evaluations to vanish. These objects are defined for every positive modulus, while primality and rank assumptions are supplied only in later density estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LocalFactors.lean#L21-L160

import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The linear part of an integer affine form after reduction modulo `p`. -/
def linearMapZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ) :
    (ι → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun x := ∑ i, (ψ.coefficient i : ZMod p) * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Evaluate an integer affine form after reducing all coefficients modulo
`p`. -/
def evalZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) : ZMod p :=
  (ψ.constant : ZMod p) + ψ.linearMapZMod p x





/-- The finite solution set of the affine congruence `ψ(x)=0 mod p`. -/
def zeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ) :
    Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ψ.linearMapZMod p x = -(ψ.constant : ZMod p)





/-- The two-output linear map defined by a pair of affine forms after
reduction modulo `p`. -/
def pairLinearMapZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ φ : AffineForm ι ℤ) :
    (ι → ZMod p) →ₗ[ZMod p] ZMod p × ZMod p :=
  (ψ.linearMapZMod p).prod (φ.linearMapZMod p)





/-- The simultaneous zero set of two affine congruences modulo `p`. -/
def commonZeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ) :
    Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ψ.evalZMod p x = 0 ∧ φ.evalZMod p x = 0















end AffineForm





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.AffineForm.commonZeroFinsetZMod.congr_simp,
    `Wikipedia.SzemeredisTheorem.AffineForm.commonZeroFinsetZMod.eq_1,
    `Wikipedia.SzemeredisTheorem.AffineForm.evalZMod.eq_1,
    `Wikipedia.SzemeredisTheorem.AffineForm.linearMapZMod.eq_1,
    `Wikipedia.SzemeredisTheorem.AffineForm.zeroFinsetZMod.congr_simp,
    `Wikipedia.SzemeredisTheorem.AffineForm.zeroFinsetZMod.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


