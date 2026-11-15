-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_mean_zeroFinsetZMod
-- name    : Wikipedia.SzemeredisTheorem.AffineForm.mean_zeroFinsetZMod
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:15.931813+00:00
-- url     : https://prove2.me/theorems/7b9f5d2a-b54b-4f45-b2a1-12f425e1e349
-- title:
--   Density of the zeros of a nondegenerate affine congruence
-- statement:
--   Let $p$ be prime and let $\psi$ be an integer affine form on a finite coordinate set $\iota$ with decidable equality. If one coefficient is nonzero modulo $p$, then the normalized mean of the indicator of its zero set over $(\mathbb Z/p\mathbb Z)^\iota$ equals $1/p$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LocalFactors.lean#L282-L299

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

theorem Wikipedia.SzemeredisTheorem.AffineForm.mean_zeroFinsetZMod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    mean (finsetIndicator (ψ.zeroFinsetZMod p)) = (1 : ℝ) / p := by sorry
