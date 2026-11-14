-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:32.81226+00:00
-- url     : https://prove2.me/theorems/f59dfde1-cd87-4de6-90dd-b47e31615c63
-- title:
--   Total, diagonal, and off-diagonal progression masses
-- statement:
--   For a real weight $f$ on the finite cyclic group $\mathbb Z/N\mathbb Z$ with $N>0$, the total $k$-term progression mass is
--
--   $$
--   \sum_a\sum_d\prod_{j=0}^{k-1}f(a+jd).
--   $$
--
--   The diagonal mass restricts the difference to $d=0$, while the off-diagonal mass sums over the finite set of nonzero differences. These masses are unnormalized, so the off-diagonal definition does not divide by $N-1$. In particular it equals zero for the one-element cyclic group, where there is no nonzero difference.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L16-L33

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The unnormalized mass of all cyclic `k`-term progressions. -/
noncomputable def cyclicAPMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cyclicAPProduct k N f a d

/-- The unnormalized contribution from constant cyclic progressions. -/
noncomputable def cyclicAPDiagonalMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cyclicAPProduct k N f a 0

/-- The unnormalized mass of cyclic progressions with nonzero common
difference.  This is zero, rather than ill-defined, if no nonzero difference
exists. -/
noncomputable def cyclicAPOffDiagMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cyclicAPProduct k N f a d



























end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cyclicAPDiagonalMass.eq_1,
    `Wikipedia.SzemeredisTheorem.cyclicAPMass.congr_simp,
    `Wikipedia.SzemeredisTheorem.cyclicAPMass.eq_1,
    `Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


