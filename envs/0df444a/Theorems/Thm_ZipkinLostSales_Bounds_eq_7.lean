-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_eq_7
-- name    : ZipkinLostSales.Bounds.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:23.541686+00:00
-- url     : https://prove2.me/theorems/8f993e52-561c-4a3d-a68d-a1208b8821a4
-- title:
--   (7), p. 940 — Nahmias's identity y₊L = z + [max_l {v_l − d_[l,L)}]⁺
-- statement:
--   Let $L\ge1$, let $v=(v_0,\dots,v_{L-1})$ be a state, $z$ the current order, and $d_t,\dots,d_{t+L-1}$ the demands of the next $L$ periods. Write $d_{[l,L)}=\sum_{j=l}^{L-1}d_{t+j}$ for the demand of periods $t+l$ through $t+L-1$. Then the inventory on hand when the current order arrives, obtained by iterating the lost-sales dynamics, is
--   $$y_{+L}=z+\Big[\max\{v_l-d_{[l,L)}:\ l=0,\dots,L-1\}\Big]^+ .$$
--
--   This closed form (due to Nahmias, 1979) expresses the only random quantity in the one-period cost $q(v,z)$ through the state; in particular $y_{+L}\ge z$. It is the starting point for the bound on the last-period policy.
--
--   **Formalization Note** The identity is deterministic and is stated for all real $v$, $z$ and demands, with no sign condition. $y_{+L}$ is the model's `yPlusL`, defined by the on-hand recursion with $x_l=v_l-v_{l+1}$, $v_L=0$; indices are $0,\dots,L-1$, and the maximum is a `Finset.sup'` over the nonempty index set, nonempty because $L\ge 1$.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), eq. (7)

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- (7), p. 940 (Nahmias 1979): `y_{+L} = z + [max{v_l − d_{[l,L)} : l = 0, …, L − 1}]⁺`, where
`d_{[l,L)} = Σ_{l ≤ j < L} D j` is the demand of periods `t + l, …, t + L − 1`. A deterministic
identity, for every real `v`, `z` and `D`. -/
theorem eq_7 {L : ℕ} (hL : 0 < L) (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    yPlusL v z D =
      z + max ((Finset.univ : Finset (Fin L)).sup' ⟨⟨0, hL⟩, Finset.mem_univ _⟩
        (fun l => v l - ∑ j ∈ Finset.Ici l, D j)) 0 := by sorry

end ZipkinLostSales.Bounds
