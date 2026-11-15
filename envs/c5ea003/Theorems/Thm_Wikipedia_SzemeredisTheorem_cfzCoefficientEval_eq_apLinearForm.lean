-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCoefficientEval_eq_apLinearForm
-- name    : Wikipedia.SzemeredisTheorem.cfzCoefficientEval_eq_apLinearForm
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:49:43.457197+00:00
-- url     : https://prove2.me/theorems/38b80c22-6a27-415f-b730-d9d802d989b9
-- title:
--   Coefficient-vector evaluation equals the canonical AP form
-- statement:
--   For natural $k,N$, a CFZ form index $q=(j,\omega)$, and a doubled cyclic vector $x$, evaluation using the CFZ coefficient vector equals the canonical AP linear form:
--
--   $$
--   \sum_{i,b}c_q(i,b)x_i^b
--   =\sum_{i\ne j}(i-j)x_i^{\omega_i}
--   \quad\text{in }\mathbb Z/N\mathbb Z.
--   $$
--
--   The identity allows every natural modulus, including zero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Independence.lean#L58-L82

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

theorem Wikipedia.SzemeredisTheorem.cfzCoefficientEval_eq_apLinearForm (k N : ℕ)
    (q : CFZFormIndex k) (x : CubePoint k N) :
    cfzCoefficientEval k N q x =
      apLinearForm k N q.1 q.2 x := by sorry
