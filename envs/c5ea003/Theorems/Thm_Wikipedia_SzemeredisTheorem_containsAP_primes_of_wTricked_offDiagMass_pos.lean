-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_containsAP_primes_of_wTricked_offDiagMass_pos
-- name    : Wikipedia.SzemeredisTheorem.containsAP_primes_of_wTricked_offDiagMass_pos
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:51:56.917615+00:00
-- url     : https://prove2.me/theorems/3c2bd325-2fcd-4613-b95d-a4ce6bdaf399
-- title:
--   Positive W-tricked progression mass yields a prime progression
-- statement:
--   Let $k,N,W,b$ be natural numbers with $k\ge2$, $N\ge1$, and $W\ge1$, and let $\alpha>0$ be real. Write $f$ for the W-tricked prime weight with parameters $(\alpha,W,b)$ on $\mathbb Z/N\mathbb Z$. If its off-diagonal cyclic $k$-term progression mass is positive, then there are natural numbers $a,d$ with $d>0$ such that
--   $$
--   \operatorname{Prime}(a+jd)\qquad(0\le j<k).
--   $$
--   No congruence or coprimality assumption on $b$ is required for this extraction implication.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/Extraction.lean#L17-L62

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
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
# Extracting a prime progression from positive W-tricked mass

This module joins the elementary end of the proof.  Once transference gives
positive off-diagonal mass for the W-tricked prime weight, no further
analytic input is needed: positivity identifies prime-supported terms,
short support unwraps the cyclic progression, and the affine W-trick lifts
it to an ordinary progression of natural primes.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.containsAP_primes_of_wTricked_offDiagMass_pos
    {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α)
    {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass :
      0 <
        cyclicAPOffDiagMass k N
          (wTrickedPrimeWeight α W b)) :
    ContainsAP {p : ℕ | Nat.Prime p} k := by sorry
