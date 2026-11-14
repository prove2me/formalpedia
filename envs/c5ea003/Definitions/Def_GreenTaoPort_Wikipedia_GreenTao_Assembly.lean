-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
-- name    : GreenTaoPort_Wikipedia_GreenTao_Assembly
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:22.547943+00:00
-- url     : https://prove2.me/theorems/cb721aae-119c-4c4c-8e84-1595eabb1437
-- title:
--   Positive prime progression mass
-- statement:
--   This predicate records the positive off-diagonal mass needed to extract prime progressions. For every integer length $k\ge3$, it asks for natural parameters $M,W,b$ and a real scale $\alpha$ with $\alpha>0$ and $W>0$, such that the $k$-term off-diagonal progression mass of the corresponding $W$-tricked prime weight on $\mathbb Z/(M+1)\mathbb Z$ is positive.
--
--   The parameter $b$ specifies the affine values $Wn+b$, and $M+1$ is a nonzero cyclic modulus. This predicate itself does not require the modulus to be prime or the residue $b$ to be coprime to $W$; those stronger properties belong to later sufficient conditions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Assembly.lean#L14-L23

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Final elementary assembly

This file states the exact remaining analytic obligation in terms of the
W-tricked prime weight.  Once positive off-diagonal mass is supplied for
every `k ≥ 3`, all conversion to the lean-eval statement is proved here.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A compact interface for the combined relative-Szemerédi and sieve
layers.  The modulus is written as `M + 1` so its nonzeroness is available
definitionally without carrying a typeclass through the existential. -/
def HasPrimeProgressionMass : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (M : ℕ) (α : ℝ) (W b : ℕ),
      0 < α ∧ 0 < W ∧
        0 <
          cyclicAPOffDiagMass k (M + 1)
            (wTrickedPrimeWeight α W b)









end Wikipedia.SzemeredisTheorem


