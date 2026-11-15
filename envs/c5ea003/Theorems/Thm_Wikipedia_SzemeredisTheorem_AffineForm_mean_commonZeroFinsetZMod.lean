-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_mean_commonZeroFinsetZMod
-- name    : Wikipedia.SzemeredisTheorem.AffineForm.mean_commonZeroFinsetZMod
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:17.940352+00:00
-- url     : https://prove2.me/theorems/ce15ae43-0744-4d4f-9951-14932983c564
-- title:
--   Density of the common zeros of two independent affine congruences
-- statement:
--   For two integer affine forms $\psi,\phi$ on a finite coordinate set $\iota$ and a prime $p$, assume that a $2\times2$ coefficient minor is nonzero modulo $p$. The normalized mean of the indicator of their common zero set over $(\mathbb Z/p\mathbb Z)^\iota$ is exactly $1/p^2$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LocalFactors.lean#L301-L321

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

theorem Wikipedia.SzemeredisTheorem.AffineForm.mean_commonZeroFinsetZMod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    mean (finsetIndicator (commonZeroFinsetZMod p ψ φ)) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by sorry
