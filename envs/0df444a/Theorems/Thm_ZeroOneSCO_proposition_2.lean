-- Prove2me | Theorems.Thm_ZeroOneSCO_proposition_2
-- name    : ZeroOneSCO.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:11.308331+00:00
-- url     : https://prove2.me/theorems/333b9016-0897-408e-a574-3c9617dd383c
-- title:
--   Proposition 2: the fixed-point inclusion $Z\in\Pi_{\mathcal S}(Z+\tau W)$
-- statement:
--   Let $W\in\mathbb R^{M\times N}$, $\tau>0$, $s\ge 1$. A point $Z\in\mathbb R^{M\times N}$ satisfies
--   $$
--   Z\in\Pi_{\mathcal S}(Z+\tau W)
--   $$
--   if and only if one of the following holds:
--
--   1. $\|Z\|_0^+<s$ and $W=0$;
--   2. $\|Z\|_0^+=s$, $W_{:\overline\Gamma_0}=0$, $0\ge Z_{:\Gamma_0}\perp W_{:\Gamma_0}\ge0$, and $\tau\|W_{:n}\|\le Z^{\downarrow}_s$ for all $n\in\Gamma_0$.
--
--   Moreover, if $Z$ satisfies the inclusion, then $\Gamma_0\in\mathbb T(Z+\tau W;s)$. Here $\Gamma_0$ is defined for $Z$.
--
--   The proposition gives the explicit meaning of the second condition of $\tau$-stationarity.
--
--   Differences from the source:
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: "𝕋(Z + τW; s) ∋ {Γ₀}" → Γ₀ ∈ 𝕋(Z + τW; s); reason: as (71) writes it; elements of 𝕋 are sets of columns
--   - encoding: the two-case display (23), silent when ‖Z‖₀⁺ > s → a disjunction of the two cases; reason: when ‖Z‖₀⁺ > s the inclusion fails, as Z ∉ 𝒮
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Proposition 2, (22), (23), p.8

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace ZeroOneSCO

/-- Proposition 2, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.8: for `τ > 0`, `Z ∈ Π_S(Z + τW)` (22)
holds if and only if (23): `W = 0` when `‖Z‖₀⁺ < s`, and when `‖Z‖₀⁺ = s`, `W_{:Γ̄₀} = 0`,
`0 ≥ Z_{:Γ₀} ⊥ W_{:Γ₀} ≥ 0` and `τ‖W_{:n}‖ ≤ Z↓_s` for all `n ∈ Γ₀`. Moreover (22) implies
`Γ₀ ∈ 𝕋(Z + τW; s)`.

**Formalization Note.** The bar over `Γ₀` in (23) is the complement (p.4), and `Γ₀ = Γ₀(Z)`. -/
theorem proposition_2 {M N : ℕ} [NeZero M] (Z W : Mat M N) (τ : ℝ) (s : ℕ) (hτ : 0 < τ)
    (hs : 0 < s) :
    (Z ∈ projS s (Z + τ • W) ↔
      (plusZero Z < s ∧ W = 0) ∨
      (plusZero Z = s ∧ (∀ n ∉ gammaZero Z, ∀ m, W m n = 0) ∧
        (∀ n ∈ gammaZero Z, ∀ m, Z m n ≤ 0 ∧ 0 ≤ W m n ∧ Z m n * W m n = 0) ∧
        ∀ n ∈ gammaZero Z, τ * colNorm W n ≤ rthLargest Z s)) ∧
    (Z ∈ projS s (Z + τ • W) → gammaZero Z ∈ TSet (Z + τ • W) s) := by sorry

end ZeroOneSCO
