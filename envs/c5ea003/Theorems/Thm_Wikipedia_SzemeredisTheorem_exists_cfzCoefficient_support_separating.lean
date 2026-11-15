-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cfzCoefficient_support_separating
-- name    : Wikipedia.SzemeredisTheorem.exists_cfzCoefficient_support_separating
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:39.254203+00:00
-- url     : https://prove2.me/theorems/0fac0b6e-4f7e-41cb-a860-15ac46e338bd
-- title:
--   Distinct CFZ forms have a separating support coordinate
-- statement:
--   For any natural $k$ and distinct CFZ form indices $q,r$, there is a doubled coordinate at which the coefficient of $q$ is zero and that of $r$ is nonzero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Independence.lean#L114-L133

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.exists_cfzCoefficient_support_separating {k : ℕ}
    (q r : CFZFormIndex k) (hqr : q ≠ r) :
    ∃ v : CFZVariable k,
      cfzCoefficient q v = 0 ∧ cfzCoefficient r v ≠ 0 := by sorry
