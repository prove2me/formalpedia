-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_pow_two_le_mean_pow_two
-- name    : Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:27:55.159659+00:00
-- url     : https://prove2.me/theorems/af73683c-34bd-4c4d-9c05-46d982e4ff95
-- title:
--   Jensen inequality for powers of two and nonnegative functions
-- statement:
--   Let $\Omega$ be a nonempty finite set, let $f:\Omega\to\mathbb R$ be nonnegative, and let $n\ge0$ be an integer. For $q=2^n$,
--   $$
--   \bigl(\mathbb E_xf(x)\bigr)^q\le\mathbb E_xf(x)^q.
--   $$
--   This is the normalized finite Jensen inequality in the form used after iterated Cauchy–Schwarz. The case $n=0$ gives exponent one and equality.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Finite/CauchySchwarz.lean#L63-L98

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

theorem Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by sorry
