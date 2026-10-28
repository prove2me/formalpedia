-- Prove2me | Theorems.Thm_ZeroFreeBridge_log_branch_of_analytic_nonvanishing
-- name    : ZeroFreeBridge.log_branch_of_analytic_nonvanishing
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:10.592986+00:00
-- url     : https://prove2.me/theorems/93118d6a-6a46-42ae-8da5-65aa02895b7d
-- title:
--   Logarithm branch on a zero-free disk
-- statement:
--   Let $r>0$ and let $g$ be holomorphic and nonvanishing on $B(c,r)$. There is a
--   function $h$ with $h(c)=\log g(c)$ such that, for every $z$ in the disk,
--   $$h'(z)=g'(z)/g(z),\qquad e^{h(z)}=g(z),\qquad
--   \operatorname{Re}h(z)=\log|g(z)|.$$
--   The value at the center uses the principal complex logarithm.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpLogBranch.lean#L27-L83

import Mathlib
/- PHASE 4 (dVP frontier, obligation (i-b') FOUNDATION): the analytic log branch of a
   zero-free function on a disk.

   The entire part `E = logDeriv g = g'/g` (from obligation (i-a)) is bounded via
   Borel-Caratheodory + Cauchy, but BC works with the REAL PART of a holomorphic function,
   and Cauchy bounds a DERIVATIVE by VALUES.  Both need `E` realised as the derivative of an
   analytic `h` with `Re h = log‖g‖`.  On a DISK a zero-free holomorphic `g` admits exactly
   such an `h` (a global branch of `log g`), built here WITHOUT the covering-map machinery:

     * `logDeriv g = g'/g` is holomorphic on the disk (denominator nonvanishing), so by Morera
       (`DifferentiableOn.isExactOn_ball`) it has a PRIMITIVE `h` with `h' = logDeriv g`;
     * pin `h c = Complex.log (g c)`;
     * `φ = g · exp(-h)` has `φ' = exp(-h)·(g' - g·(g'/g)) = 0`, so `φ` is constant on the
       convex disk, `= φ c = g c / g c = 1`; hence `exp∘h = g`;
     * `‖g‖ = ‖exp h‖ = exp(Re h)` gives `Re h = log‖g‖`.

   Output packages `h` differentiable, `deriv h = logDeriv g`, `exp∘h = g`, `Re h = log‖g‖` —
   the object BC and Cauchy consume to bound `‖E‖ ≤ A·L`.  Function-agnostic (any analytic
   zero-free `g`).  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.log_branch_of_analytic_nonvanishing {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt h (logDeriv g z) z) ∧
      h c = Complex.log (g c) ∧
      (∀ z ∈ ball c r, Complex.exp (h z) = g z) ∧
      (∀ z ∈ ball c r, (h z).re = Real.log ‖g z‖) := by sorry
