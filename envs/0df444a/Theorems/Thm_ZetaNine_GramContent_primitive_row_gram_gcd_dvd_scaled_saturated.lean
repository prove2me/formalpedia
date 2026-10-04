-- Prove2me | Theorems.Thm_ZetaNine_GramContent_primitive_row_gram_gcd_dvd_scaled_saturated
-- name    : ZetaNine.GramContent.primitive_row_gram_gcd_dvd_scaled_saturated
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:34:03.898035+00:00
-- url     : https://prove2.me/theorems/17f19266-744f-4790-b31a-e7c5c18ca549
-- title:
--   Primitive-row Gram content divides the scaled divided determinant
-- statement:
--   Let $u,v\in\mathbb Z^d$, with $u$ primitive, and let $\Delta\ne0$ divide every minor $u_iv_j-u_jv_i$. Put $T=\langle u,u\rangle$, $C=\langle u,v\rangle$, $R=\langle v,v\rangle$ and $D_\Delta=(TR-C^2)/\Delta^2$. Then
--
--   $$\gcd(T,C)\mid \Delta D_\Delta.$$
--
--   Primitivity means that the coordinates of $u$ admit an integral Bézout combination equal to one. The theorem covers every finite dimension and every nonzero common minor divisor, including the exterior content. It does not assume squarefreeness, linear independence or nondegeneracy modulo any prime.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/direction-arithmetic-next-2026-10-02.md, section 1, equations (1) and (5).

import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
open scoped BigOperators
open ZetaNine.GramContent

theorem ZetaNine.GramContent.primitive_row_gram_gcd_dvd_scaled_saturated {ι : Type*} [Fintype ι] (u v : ι → ℤ) (Δ : ℤ)
    (hprimitive : ∃ a : ι → ℤ, (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by sorry
