-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_card_commonZeroFinsetZMod_mul
-- name    : Wikipedia.SzemeredisTheorem.AffineForm.card_commonZeroFinsetZMod_mul
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:18.084612+00:00
-- url     : https://prove2.me/theorems/e7ed1c8d-b42b-4a70-a041-df5c1b14e766
-- title:
--   Cardinality of the common zeros of two independent affine congruences
-- statement:
--   Let $\iota$ be a finite type with decidable equality, let $p$ be prime, and let $\psi,\phi$ be integer-valued affine forms in variables indexed by $\iota$. If some $2\times2$ coefficient minor is nonzero modulo $p$, then their common zero set $Z$ over $\mathbb Z/p\mathbb Z$ satisfies $p^2|Z|=p^{|\iota|}$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LocalFactors.lean#L171-L230

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

theorem Wikipedia.SzemeredisTheorem.AffineForm.card_commonZeroFinsetZMod_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    p ^ 2 * (commonZeroFinsetZMod p ψ φ).card =
      p ^ Fintype.card ι := by sorry
