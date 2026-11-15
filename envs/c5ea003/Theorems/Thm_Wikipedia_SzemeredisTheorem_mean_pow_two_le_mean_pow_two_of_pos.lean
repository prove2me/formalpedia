-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_pow_two_le_mean_pow_two_of_pos
-- name    : Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two_of_pos
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:33.67444+00:00
-- url     : https://prove2.me/theorems/70fadf2a-cfd5-482f-86aa-3c5745b2dd03
-- title:
--   Jensen inequality for even powers of two
-- statement:
--   Let $\Omega$ be a nonempty finite set, let $f:\Omega\to\mathbb R$ be arbitrary, and let $n\ge1$ be an integer. Setting $q=2^n$, one has
--   $$
--   \bigl(\mathbb E_xf(x)\bigr)^q\le\mathbb E_xf(x)^q.
--   $$
--   Here $q$ is even, so no nonnegativity assumption on $f$ is needed. The hypothesis on $n$ is stronger than mere positivity of the exponent $q$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Finite/CauchySchwarz.lean#L100-L124

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two_of_pos
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {n : ℕ} (hn : 0 < n) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by sorry
