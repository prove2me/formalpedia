-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_lemma_6
-- name    : ZipkinLostSales.Bounds.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:39.500482+00:00
-- url     : https://prove2.me/theorems/c495d10d-fba3-4e00-91c9-142161e9fa50
-- title:
--   Lemma 6, p. 940 — the last-period policy z̄_T(v) is in Z(s̄)
-- statement:
--   Consider the lost-sales model of §4 under its standing assumptions (i.i.d. nonnegative demand with finite mean, $c,\hat h,p\ge 0$, $0<\gamma\le1$, $0<c+h<p+h$ with $h=\hat h-\gamma c$). In the last period $T$ the function to be minimized is the one-period cost $g_T(v,z)=q(v,z)=\gamma^L E[q^0(y_{+L})]$. For every state $v\in V$, the smallest minimizer $\bar z_T(v)$ of $q(v,\cdot)$ over $z\ge0$ exists and satisfies the bounds of $Z(\bar s)$:
--   $$v\notin V(\bar s)\ \Rightarrow\ \bar z_T(v)=0,\qquad v\in V(\bar s)\ \Rightarrow\ \bar z_T(v)\le\bar s_L\ \text{ and }\ v_l+\bar z_T(v)\le \bar s_l\ \ (l=0,\dots,L-1).$$
--
--   This is the base case of the bounds: the myopic order is limited by the fractiles (6) of the lead-time demand.
--
--   **Formalization Note** $t=T$ is $k=0$ periods of continuation, where $g_T=q$ (with $f_{T+1}=0$). "The policy $\bar z_T(v)$" is read as the least minimizer, and its existence is part of the statement. The statement is about §4's recursion; its identification with §2's optimal policy ("some algebra", p. 940) is not formalized. The finite mean and the sign conventions on $c,\hat h,p,\gamma$ are added readings of §2.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), Lemma 6

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Lemma 6, p. 940: the policy `z̄_T(v)` is in `Z(s̄)`. With one period to go (`k = 0`,
`t = T`), for every `v ∈ ZipkinLostSales.LNatural.V` the smallest minimizer of `g_T(v, ·) = q(v, ·)` over `z ≥ 0` exists and
satisfies the bounds of `Z(s̄)` at `v`. -/
theorem lemma_6 {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) :
    ∃ z : ℝ, IsOptOrder M 0 v z ∧ InZ L M v z := by sorry

end ZipkinLostSales.Bounds
