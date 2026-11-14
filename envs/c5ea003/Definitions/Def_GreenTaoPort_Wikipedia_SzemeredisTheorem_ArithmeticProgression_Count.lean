-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:45.055482+00:00
-- url     : https://prove2.me/theorems/2c037ae1-1f2b-4fe5-a7dd-8b313ddbffa7
-- title:
--   Normalized weighted counts of cyclic arithmetic progressions
-- statement:
--   For a natural length $k$ and residues $a,d\in\mathbb Z/N\mathbb Z$, the $j$th progression term is $a+jd$. A real weight $f$ assigns the progression the product
--
--   $$
--   P_f(a,d)=\prod_{j=0}^{k-1}f(a+jd).
--   $$
--
--   When $N>0$, the normalized cyclic count is the average of $P_f(a,d)$ over both $a$ and $d$. It includes the constant progressions with $d=0$. Empty products give value one at length zero; the weight is not assumed nonnegative in these definitions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/Count.lean#L17-L30

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.ZMod.Basic
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The `j`th term of a cyclic arithmetic progression. -/
def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

/-- The weight contributed by one cyclic `k`-term progression. -/
def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

/-- The normalized weighted count of cyclic `k`-term progressions. The
average includes the diagonal `d = 0`. -/
noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cyclicAPCount.congr_simp,
    `Wikipedia.SzemeredisTheorem.cyclicAPCount.eq_1,
    `Wikipedia.SzemeredisTheorem.cyclicAPProduct.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


