-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_le_majorant
-- name    : Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_majorant
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:10.718199+00:00
-- url     : https://prove2.me/theorems/f843e7e2-477c-42a1-8553-d129916b5fef
-- title:
--   A logarithmic comparison gives prime-weight domination
-- statement:
--   Let $N\ne0$, $R>1$, $W>0$, and $c_\chi>0$. Suppose a real cutoff satisfies $\chi(0)=1$ and vanishes on $[1,\infty)$. Assume that whenever a residue representative lies in the Green–Tao interval and its W-tricked value is prime, that value exceeds $R$ and $\alpha\log(\operatorname{wTrickedValue})\le\log R/c_\chi$. Then the W-tricked prime weight is pointwise bounded by the corresponding W-tricked majorant.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrick.lean#L154-L184

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
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
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_majorant
    {N : ℕ} [NeZero N]
    {α cχ : ℝ} (hcχ : 0 < cχ)
    {R W b : ℕ} (hR : 1 < R) (hW : 0 < W)
    (χ : ℝ → ℝ) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hscale :
      ∀ n : ZMod N,
        n.val ∈ greenTaoInterval N →
        Nat.Prime (wTrickedValue W b n) →
        R < wTrickedValue W b n ∧
          α * Real.log (wTrickedValue W b n) ≤
            Real.log R / cχ) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        wTrickedMajorant χ cχ R W b n := by sorry
