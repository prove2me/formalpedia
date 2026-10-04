-- Prove2me | Theorems.Thm_ZetaNine_CenterDenominator_primitive_center_denominator_divisor
-- name    : ZetaNine.CenterDenominator.primitive_center_denominator_divisor
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:34:14.199204+00:00
-- url     : https://prove2.me/theorems/b3c67d4e-0f05-484e-b795-af057457788e
-- title:
--   Explicit divisor of the content-adjusted center denominator
-- statement:
--   Let $u,v\in\mathbb Z^d$, with $u$ primitive, and let $\Delta\ne0$ divide every exterior minor. Put $T=\langle u,u\rangle$, $C=\langle u,v\rangle$ and $D_\Delta=(T\langle v,v\rangle-C^2)/\Delta^2$. For any integers $a\ne0$ and $b$, the center $\xi=bC/(aT)$ satisfies
--
--   $$\frac{T}{\gcd(T,b\Delta D_\Delta)}\mid\operatorname{den}(\xi).$$
--
--   Primitivity guarantees $T>0$. Neither coprimality of $a,b$ nor primitiveness of $v$ is required. For primitive row reductions and their content ratio this is the computable divisor in equation (6). It asserts an exact denominator divisor, not the still-unproved exponential growth needed for the irrationality route.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/direction-arithmetic-next-2026-10-02.md, section 2, equation (6).

import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
open scoped BigOperators
open ZetaNine.GramContent

theorem ZetaNine.CenterDenominator.primitive_center_denominator_divisor {ι : Type*} [Fintype ι] (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by sorry
