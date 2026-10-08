-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_theorem_8
-- name    : ZipkinLostSales.Bounds.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:33.6681+00:00
-- url     : https://prove2.me/theorems/e9d13d66-1a5d-4215-bfe6-fdfa6b3dcfcf
-- title:
--   Theorem 8, p. 940 — for all t ≤ T, f_t(v) is nondecreasing in v and z̄_t(v) ≤ z̄_T(v)
-- statement:
--   Consider the lost-sales model of §4 under its standing assumptions. For every period $t\le T$:
--
--   1. the optimal cost $f_t(v)$ is nondecreasing on $V$ for the componentwise order;
--   2. for every $v\in V$, the optimal order is at most the last-period one:
--   $$\bar z_t(v)\le \bar z_T(v).$$
--
--   Here $\bar z_t(v)$ is the smallest minimizer of $g_t(v,\cdot)$ over $z\ge0$. With Lemma 6, part 2 shows that the bounds $Z(\bar s)$ hold in every period.
--
--   **Formalization Note** Period $t=T-k$ is indexed by $k\ge0$: $f_t$ is `fB M (k+1)` and $\bar z_t$ is the least minimizer of `gB M k`; $\bar z_T$ is the least minimizer of `gB M 0` $=q$. Part 2 asserts that the least minimizers $z$ of $g_t(v,\cdot)$ and $z'$ of $g_T(v,\cdot)$ exist and satisfy $z\le z'$. The identification of §4's recursion with §2's is not formalized.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), Theorem 8

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Theorem 8, p. 940: for all `t ≤ T` (every `k`, `t = T − k`), `f_t(v)` is nondecreasing in `v`
on `V`, and the smallest optimal orders `z̄_t(v)` and `z̄_T(v)` exist and satisfy
`z̄_t(v) ≤ z̄_T(v)`. -/
theorem theorem_8 {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) :
    MonotoneOn (fB M (k + 1)) (ZipkinLostSales.LNatural.V L) ∧
      ∀ v ∈ ZipkinLostSales.LNatural.V L,
        ∃ z z' : ℝ, IsOptOrder M k v z ∧ IsOptOrder M 0 v z' ∧ z ≤ z' := by sorry

end ZipkinLostSales.Bounds
