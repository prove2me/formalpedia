-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.AffineForm.mean_zeroFinsetZMod
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:03.893444+00:00
-- url     : https://prove2.me/submissions/1bc8d4c5-75b7-4b5a-8544-bed9437a95c5

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_card_zeroFinsetZMod_mul

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

























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
/-- The exact normalized density of one nondegenerate affine congruence. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    mean (finsetIndicator (ψ.zeroFinsetZMod p)) = (1 : ℝ) / p := by
  rw [mean_finsetIndicator, Fintype.card_fun, ZMod.card]
  have hcard := card_zeroFinsetZMod_mul hp ψ hi
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpow0 : ((p : ℝ) ^ Fintype.card ι) ≠ 0 :=
    pow_ne_zero _ hp0
  have hcardR :
      (p : ℝ) * ((ψ.zeroFinsetZMod p).card : ℝ) =
        (p : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hcard
  field_simp
  simpa [mul_comm] using hcardR
