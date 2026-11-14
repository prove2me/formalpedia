-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
-- name    : GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:34.293932+00:00
-- url     : https://prove2.me/theorems/0f9d00b2-091e-4da4-846e-e6a92c4ca141
-- title:
--   Sampling and untricking primes in a residue class
-- statement:
--   For natural parameters $W,N$, the sampling scale is $X=W\lfloor N/8\rfloor$. The selected prime set consists of the primes in $(\lfloor X/4\rfloor,X]$ whose remainder modulo $W$ is $b$.
--
--   A selected prime $p$ is sent to the natural parameter
--
--   $$
--   u(p)=\frac{p-b}{W}
--   $$
--
--   using natural subtraction and quotient, and then to its image in $\mathbb Z/N\mathbb Z$. The resulting finite cyclic set is the image of the selected primes under this map. In the positive-modulus residue-class setting, $p=Wu(p)+b$; the definitions themselves are total at arbitrary natural parameters. This sampling scale is chosen so that later bounds place the untricked points in the short interval used by the prime weight.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L21-L147

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/

namespace Wikipedia.SzemeredisTheorem

open Finset Real Filter
open scoped BigOperators

/-- The scale at which primes are sampled before applying the `W`-trick. -/
def wTrickPrimeScale (W N : ℕ) : ℕ :=
  W * (N / 8)

/-- The primes in `(X / 4, X]`, where `X = W * (N / 8)`, which lie in the
standard residue class `b` modulo `W`. -/
def quarterIntervalResidueClass (W N b : ℕ) : Finset ℕ :=
  residueFiber (primesInQuarterInterval (wTrickPrimeScale W N)) W b



/-- The natural parameter underlying a prime in residue class `b`. -/
def untrickPrime (W b p : ℕ) : ℕ :=
  (p - b) / W

/-- The same parameter, regarded as an element of the cyclic group. -/
def untrickPrimeZMod (N W b p : ℕ) : ZMod N :=
  (untrickPrime W b p : ℕ)

















/-- The image of the selected primes inside the cyclic group. -/
def untrickedPrimeResidues (N W b : ℕ) : Finset (ZMod N) :=
  (quarterIntervalResidueClass W N b).image
    (untrickPrimeZMod N W b)













































end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.quarterIntervalResidueClass.eq_1,
    `Wikipedia.SzemeredisTheorem.untrickPrime.eq_1,
    `Wikipedia.SzemeredisTheorem.untrickedPrimeResidues.eq_1,
    `Wikipedia.SzemeredisTheorem.wTrickPrimeScale.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


