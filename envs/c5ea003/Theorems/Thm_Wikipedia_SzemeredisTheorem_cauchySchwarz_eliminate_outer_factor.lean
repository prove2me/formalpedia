-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cauchySchwarz_eliminate_outer_factor
-- name    : Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_factor
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:48:48.04114+00:00
-- url     : https://prove2.me/theorems/799eee8e-a06f-4c23-aca2-a4719647b19c
-- title:
--   Cauchy–Schwarz eliminates a bounded outer factor
-- statement:
--   Let $X$ be a nonempty finite type and $Y$ a finite type. For real functions $u:X\to\mathbb R$ and $F:X\times Y\to\mathbb R$ with $|u(x)|\le1$,
--
--   $$
--   \left(\mathbb E_{x,y}u(x)F(x,y)\right)^2
--   \le\mathbb E_{x,y_0,y_1}F(x,y_0)F(x,y_1).
--   $$
--
--   No sign condition on $F$ or nonemptiness condition on $Y$ is required.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Finite/CauchySchwarz.lean#L139-L174

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

theorem Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_factor
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (u : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by sorry
