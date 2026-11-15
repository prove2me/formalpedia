-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCoefficient_natAbs_le
-- name    : Wikipedia.SzemeredisTheorem.cfzCoefficient_natAbs_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:49:45.09683+00:00
-- url     : https://prove2.me/theorems/fe8b50bf-e375-4d89-8eb2-5da9072deeb1
-- title:
--   CFZ coefficients have absolute value at most the progression length
-- statement:
--   For a natural progression length $k$, a CFZ form index $q$, and a doubled-variable coordinate $v$, the integer coefficient satisfies $|c_q(v)|\le k$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Geometry.lean#L82-L97

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.cfzCoefficient_natAbs_le {k : ℕ}
    (q : CFZFormIndex k) (v : CFZVariable k) :
    Int.natAbs (cfzCoefficient q v) ≤ k := by sorry
