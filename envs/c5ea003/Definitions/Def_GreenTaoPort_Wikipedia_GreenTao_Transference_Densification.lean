-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:54.32011+00:00
-- url     : https://prove2.me/theorems/5dab8569-4d5c-4624-81f8-add851c2cdf8
-- title:
--   Projected majorant moments and truncation at one
-- statement:
--   On a finite type $\Omega$, the projected-moment hypothesis for a real majorant $\nu$ and error $\eta$ records $\eta\ge0$, pointwise nonnegativity of $\nu$, and
--
--   $$
--   |\mathbb E\nu-1|\le\eta,\qquad
--   |\mathbb E\nu^2-1|\le\eta.
--   $$
--
--   The pointwise truncation of a real function $g$ is $\min(g,1)$, and its excess above one is $\max(g-1,0)$. Truncation alone does not impose a lower bound on an arbitrary input; with a nonnegative input it gives a weight in $[0,1]$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/Densification.lean#L31-L132

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Finite analytic lemmas for densification

This file isolates the elementary projected-majorant estimates used in one
step of Conlon--Fox--Zhao densification.  It does not state a relative
counting theorem.

If a nonnegative finite majorant `ν` has first and second normalized moments
within `η` of one, then

```
mean (fun x => |ν x - 1|) ≤ √(3 * η).
```

For `0 ≤ g ≤ ν`, truncating `g` pointwise at one produces a `[0,1]`-valued
function.  Its `L¹` loss, and its loss in any pairing against a unit-bounded
factor, are bounded first by the mean excess `max (ν - 1) 0`, and hence by
the same square-root moment bound.  The final section records pointwise and
averaged product-perturbation inequalities used to package the remaining
bounded factors in a densification step.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projected-majorant moments -/

/-- The finite moment hypotheses used after projecting all majorant factors
other than the edge currently being densified.

The common error parameter is recorded as nonnegative so downstream
square-root statements do not have to recover this fact from an absolute
value inequality. -/
structure HasProjectedMajorantMoments
    {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (η : ℝ) : Prop where
  error_nonneg : 0 ≤ η
  nonneg : ∀ x, 0 ≤ ν x
  firstMoment_close : |mean ν - 1| ≤ η
  secondMoment_close :
    |mean (fun x => ν x ^ 2) - 1| ≤ η



namespace HasProjectedMajorantMoments







end HasProjectedMajorantMoments

/-! ## Truncation at one -/

/-- Pointwise truncation used to turn a nonnegative function into a dense
`[0,1]` model. -/
def truncateAtOne {Ω : Type*} (g : Ω → ℝ) : Ω → ℝ :=
  fun x => min (g x) 1

/-- Pointwise mass above one. -/
def excessAboveOne {Ω : Type*} (f : Ω → ℝ) : Ω → ℝ :=
  fun x => max (f x - 1) 0





























namespace HasProjectedMajorantMoments







end HasProjectedMajorantMoments

/-! ## Pairing and product perturbations -/





namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments











namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.excessAboveOne.eq_1,
    `Wikipedia.SzemeredisTheorem.truncateAtOne.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


