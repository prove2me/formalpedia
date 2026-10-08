-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_corollary_9
-- name    : ZipkinLostSales.Bounds.corollary_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:41.1045+00:00
-- url     : https://prove2.me/theorems/c47a69ec-2cee-44ee-95c3-150f9cf41855
-- title:
--   Corollary 9 (Karlin–Scarf 1958, Morton 1969), p. 940 — for all t ≤ T, the policy z̄_t(v) is in Z(s̄)
-- statement:
--   Consider the lost-sales inventory model with lead time $L\ge1$ in the re-accounted form of §4: i.i.d. nonnegative demand with finite mean, cost factors $c,\hat h,p\ge0$, discount factor $0<\gamma\le1$, $h=\hat h-\gamma c$, and the assumption $0<c+h<p+h$. Let $f_t$, $g_t$ be the optimal costs of the recursion
--   $$f_t(v)=\min_{z\ge0}\big\{q(v,z)+\gamma E[f_{t+1}(v_+)]\big\},\qquad f_{T+1}=0,$$
--   and $\bar z_t(v)$ the smallest optimal order. Let $\bar s_0,\dots,\bar s_L$ be the fractiles (6) of the $(L-l+1)$-period demand at level $1-\bar\theta$, $\bar\theta=(c+h)/(p+h)$.
--
--   Then for every period $t\le T$ and every state $v\in V$ the smallest optimal order $\bar z_t(v)$ exists and lies in $Z(\bar s)$:
--   $$\bar z_t(v)=0\ \text{ if } v\notin V(\bar s);\qquad \bar z_t(v)\le\bar s_L\ \text{ and }\ v_l+\bar z_t(v)\le\bar s_l\ \ (l=0,\dots,L-1)\ \text{ if } v\in V(\bar s).$$
--
--   These are the bounds of Karlin and Scarf (1958) and Morton (1969): the optimal lost-sales order never exceeds the order-up-to quantities computed from the fractiles of the lead-time demand, and no order is placed once any partial inventory position exceeds its fractile.
--
--   **Formalization Note** Periods are indexed by $k=T-t\ge0$; by stationarity "for all $t\le T$" is "for all $k$". The minimum in the recursion is an infimum over $z\ge0$, and "the policy $\bar z_t(v)$" is the least minimizer (`IsLeast`), whose existence is asserted. Everything is stated for §4's recursion; the paper's identification of its optimal policy with that of §2 ("some algebra", p. 940) is not formalized. The finite mean of demand and the sign conventions on $c,\hat h,p,\gamma$ are added readings of §2.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), Corollary 9

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Corollary 9, p. 940 (Karlin and Scarf 1958, Morton 1969): for all `t ≤ T`, the policy `z̄_t(v)`
is in `Z(s̄)`. For every number `k` of further periods and every `v ∈ ZipkinLostSales.LNatural.V`, the smallest minimizer of
`g_t(v, ·)` over `z ≥ 0` (`t = T − k`) exists and satisfies the bounds of `Z(s̄)` at `v`. -/
theorem corollary_9 {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L) : ∃ z : ℝ, IsOptOrder M k v z ∧ InZ L M v z := by sorry

end ZipkinLostSales.Bounds
