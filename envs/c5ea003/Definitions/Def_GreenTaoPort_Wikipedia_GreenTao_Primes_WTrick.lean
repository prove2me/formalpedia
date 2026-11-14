-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
-- name    : GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:25.230684+00:00
-- url     : https://prove2.me/theorems/d9858ebe-3ec8-43b9-8e31-d4669207752e
-- title:
--   Localized prime weights and Selberg majorants
-- statement:
--   Let $N>0$ be a cyclic modulus, and represent $n\in\mathbb Z/N\mathbb Z$ by its standard natural value $t$. The localization interval is
--
--   $$
--   I_N=[\lfloor N/64\rfloor,\lfloor N/4\rfloor]\cap\mathbb N.
--   $$
--
--   For a real scale $\alpha$ and natural affine parameters $W,b$, the prime weight is zero unless $t\in I_N$ and $Wt+b$ is prime. In that case it equals
--
--   $$
--   \alpha\,\frac{\varphi(W)}{W}\log(Wt+b).
--   $$
--
--   The companion majorant uses a smoothing function $\chi$, normalizer $c_\chi$, and sieve level $R$: inside $I_N$ it is the normalized Selberg square evaluated at $Wt+b$, and outside $I_N$ it is one. The positive-period and positive-normalizer hypotheses needed for later estimates are not built into these total definitions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrick.lean#L17-L59

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Data.ZMod.Basic
import Lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The fixed short interval used to prevent wraparound when a cyclic
progression is lifted back to the natural numbers. -/
def greenTaoInterval (N : ℕ) : Finset ℕ :=
  Finset.Icc (N / 64) (N / 4)





/-- The affine natural number represented by a W-tricked residue. -/
def wTrickedValue {N : ℕ} [NeZero N]
    (W b : ℕ) (n : ZMod N) : ℕ :=
  W * n.val + b

/-- Localized, logarithmically weighted indicator of W-tricked primes. -/
noncomputable def wTrickedPrimeWeight {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ) (n : ZMod N) : ℝ :=
  if n.val ∈ greenTaoInterval N ∧ Nat.Prime (wTrickedValue W b n) then
    α * ((W.totient : ℝ) / W) * Real.log (wTrickedValue W b n)
  else
    0

/-- Localized Selberg majorant. -/
noncomputable def wTrickedMajorant {N : ℕ} [NeZero N]
    (χ : ℝ → ℝ) (cχ : ℝ) (R W b : ℕ) (n : ZMod N) : ℝ :=
  if n.val ∈ greenTaoInterval N then
    normalizedSelbergMajorant χ cχ R W (wTrickedValue W b n)
  else
    1















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.greenTaoInterval.eq_1,
    `Wikipedia.SzemeredisTheorem.wTrickedMajorant.eq_1,
    `Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.wTrickedValue.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


