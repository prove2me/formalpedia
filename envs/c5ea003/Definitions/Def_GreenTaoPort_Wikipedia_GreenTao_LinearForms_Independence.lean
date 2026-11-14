-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
-- name    : GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:29.815324+00:00
-- url     : https://prove2.me/theorems/15813efc-bcff-4563-a65d-be02a04fcef1
-- title:
--   The doubled Conlon–Fox–Zhao coefficient system
-- statement:
--   For a natural length $k$, a form index consists of a deleted coordinate $j\in\{0,\ldots,k-1\}$ and a Boolean choice $\omega$ on the remaining coordinates. Variables are pairs $(i,b)$ with $i\in\{0,\ldots,k-1\}$ and $b\in\{0,1\}$. The integer coefficient is
--
--   $$
--   c_{j,\omega}(i,b)=
--   \begin{cases}i-j,&i\ne j\text{ and }b=\omega(i),\\0,&\text{otherwise}.\end{cases}
--   $$
--
--   The corresponding evaluation sums these coefficients against a doubled variable vector in $\mathbb Z/N\mathbb Z$. A separate predicate on integer vectors $c_1,c_2$ declares them proportional precisely when $c_1(v)c_2(w)=c_1(w)c_2(v)$ for all coordinates $v,w$. This avoids choosing a ratio and applies even to zero vectors.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Independence.lean#L13-L140

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Lean
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

namespace Wikipedia.SzemeredisTheorem

/-- A nondependent index for the CFZ family: a deleted coordinate together
with a vertex of the remaining Boolean cube. -/
abbrev CFZFormIndex (k : ℕ) :=
  Σ j : Fin k, DeletedCube k j

/-- The doubled variables used by the CFZ forms. -/
abbrev CFZVariable (k : ℕ) :=
  Fin k × Bool

/-- The integer coefficient of a doubled variable in a CFZ form. -/
def cfzCoefficient {k : ℕ} (q : CFZFormIndex k)
    (v : CFZVariable k) : ℤ :=
  if h : v.1 ≠ q.1 then
    if v.2 = q.2 ⟨v.1, h⟩ then
      (v.1 : ℤ) - (q.1 : ℤ)
    else
      0
  else
    0

/-- Evaluate the integer coefficient vector in `ZMod N` on a doubled
variable vector. -/
noncomputable def cfzCoefficientEval (k N : ℕ)
    (q : CFZFormIndex k) (x : CubePoint k N) : ZMod N :=
  ∑ v : CFZVariable k,
    (cfzCoefficient q v : ZMod N) * x v.1 v.2

















/-- Two integer coefficient vectors are proportional when all their
two-by-two minors vanish.  For nonzero vectors this is equivalent to
proportionality over `ℚ`, while avoiding a choice of orientation or ratio. -/
def IntCoefficientProportional {ι : Type*}
    (c₁ c₂ : ι → ℤ) : Prop :=
  ∀ v w, c₁ v * c₂ w = c₁ w * c₂ v



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCoefficient.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCoefficientEval.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


