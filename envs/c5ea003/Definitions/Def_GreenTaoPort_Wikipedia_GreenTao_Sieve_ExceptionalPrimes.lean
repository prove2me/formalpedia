-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:51:55.629263+00:00
-- url     : https://prove2.me/theorems/7e0546fa-84d8-438a-84ac-c7e29fa538cd
-- title:
--   Explicit coefficient and minor bounds for affine systems
-- statement:
--   For integer affine forms $\psi,\phi$ with coefficient vectors indexed by a type $I$, their coefficient minor at $i,j\in I$ is
--
--   $$
--   \Delta_{ij}(\psi,\phi)=\psi_i\phi_j-\psi_j\phi_i.
--   $$
--
--   For a finite family $(\psi_q)_{q\in K}$ on a finite variable set $I$, the exceptional-prime bound is the sum of the absolute values of every coefficient and every ordered two-form minor. It is a natural number, with repeated or zero terms allowed. This coarse explicit bound is used later to ensure that selected nonzero coefficients and minors remain nonzero modulo a larger prime; no independence hypothesis is built into the definition itself.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ExceptionalPrimes.lean#L16-L48

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
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

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm

/-- A two-by-two minor of two integer coefficient vectors. -/
def coefficientMinor {ι : Type*}
    (ψ φ : AffineForm ι ℤ) (i j : ι) : ℤ :=
  ψ.coefficient i * φ.coefficient j -
    ψ.coefficient j * φ.coefficient i

end AffineForm



/-- A coarse explicit bound containing every coefficient and every ordered
two-form minor in the system. -/
def exceptionalPrimeBound {κ ι : Type*}
    [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : ℕ :=
  (∑ q : κ, ∑ i : ι,
      Int.natAbs ((forms q).coefficient i)) +
    ∑ q : κ, ∑ r : κ, ∑ i : ι, ∑ j : ι,
      Int.natAbs ((forms q).coefficientMinor (forms r) i j)











end Wikipedia.SzemeredisTheorem


