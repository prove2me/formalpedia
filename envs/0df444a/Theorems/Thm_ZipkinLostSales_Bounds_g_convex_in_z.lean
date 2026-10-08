-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_g_convex_in_z
-- name    : ZipkinLostSales.Bounds.g_convex_in_z
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:38.285976+00:00
-- url     : https://prove2.me/theorems/c8107d55-8748-4469-901a-2e989013e5ef
-- title:
--   Proof of Theorem 8, p. 940 — g_t(v, z) = q(v, z) + γE[f_{t+1}(v₊)] is convex in z
-- statement:
--   Consider the lost-sales model of §4 under its standing assumptions. For every period $t\le T$ and every state $v\in V$, the function
--   $$z\ \longmapsto\ g_t(v,z)=q(v,z)+\gamma E\big[f_{t+1}(v_+)\big]$$
--   is convex on $z\ge0$, where $v_+=([v_0-v_1-d]^+ + v_1, v_2,\dots,v_{L-1},0)+z e$ and $d$ is the demand of period $t$.
--
--   Convexity in the order is the step of the proof of Theorem 8 that turns "$E[f_{t+1}(v_+)]$ is nondecreasing in $z$" into the monotonicity of $f_t$, "as in Lemma 7".
--
--   **Formalization Note** "For all $t\le T$" is "for every number $k\ge0$ of continuation periods": `gB M k` is $g_{T-k}$. The paper obtains the claim from Theorem 4 (L♮-convexity in §2's model) and the fact that §4's $g_t$ differs from §2's $\bar g_t(v,-z)$ by a term independent of $z$; that identification is not formalized, so the claim is posed directly for §4's recursion.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), proof of Theorem 8

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Proof of Theorem 8, p. 940: for every `t ≤ T` (every `k`) and every `v ∈ ZipkinLostSales.LNatural.V`,
`g_t(v, z) = q(v, z) + γE[f_{t+1}(v₊)]` is convex in `z` on `z ≥ 0`. -/
theorem g_convex_in_z {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L) : ConvexOn ℝ (Set.Ici 0) (gB M k v) := by sorry

end ZipkinLostSales.Bounds
