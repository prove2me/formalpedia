-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_minor_natAbs_le_exceptionalPrimeBound
-- name    : Wikipedia.SzemeredisTheorem.minor_natAbs_le_exceptionalPrimeBound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:20.088032+00:00
-- url     : https://prove2.me/theorems/28025d94-10d9-4c50-aa4f-517f99fdd6d4
-- title:
--   Coefficient minors are bounded by the exceptional-prime bound
-- statement:
--   Let $\kappa$ and $\iota$ be finite index sets, and let $(L_q)_{q\in\kappa}$ be integer affine forms in variables indexed by $\iota$. For any $q,r\in\kappa$ and $i,j\in\iota$, their coefficient minor satisfies
--   $$
--   \left|\det\begin{pmatrix}a_{q,i}&a_{q,j}\\a_{r,i}&a_{r,j}\end{pmatrix}\right|
--   \le B(L),
--   $$
--   where $a_{q,i}$ is the coefficient of the $i$th variable in $L_q$ and $B(L)$ is the exceptional-prime bound attached to the family. Repeated row or column indices are allowed.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ExceptionalPrimes.lean#L72-L130

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
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
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.minor_natAbs_le_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ)
    (q r : κ) (i j : ι) :
    Int.natAbs
        ((forms q).coefficientMinor (forms r) i j) ≤
      exceptionalPrimeBound forms := by sorry
