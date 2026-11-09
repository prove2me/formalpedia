-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_acceptance_criterion
-- name    : ZLIPPadding.Padding.acceptance_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:48.792101+00:00
-- url     : https://prove2.me/theorems/eea299eb-5753-4cf7-8945-b4cd197e39b4
-- title:
--   Lemma 7.4 — Acceptance criterion
-- statement:
--   Let $n$ be positive, $M\in\mathrm{GL}_n(\mathbb Z)$, $G=M^TM$, and let $a\in\mathbb Z^n$ be the projected coordinates. Write $J=|\operatorname{supp}(Ma)|$. The screen rejects $a=0$; otherwise it computes $g=\gcd(a)$ and $a_0=a/g$, and accepts exactly when $a_0^TGa_0=1$. Then
--   $$\text{screen accepts}\ \Longleftrightarrow\ J=1.$$
--   Every accepted answer has $a_0^TGa_0=1$, equivalently $Ba_0\in S_1(L)$ for an ambient basis with Gram matrix $G$. This makes the hidden singleton event recognizable from public coordinates alone.
--
--   Differences from the source:
--   - encoding: every accepted geometric vector Ba₀ belongs to S₁(L) → every accepted coordinate vector a₀ satisfies a₀ᵀGa₀=1; reason: G=BᵀB, so these are equivalent for every ambient basis B with Gram matrix G
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 30 (PDF p. 31), Lemma 7.4

import Definitions.Def_ZLIPPadding_Padding_GramModel

namespace ZLIPPadding.Padding
/-- Lemma 7.4, printed p.30 / PDF p.31. Includes a=0, arbitrary signs and multiples. -/
theorem acceptance_criterion (n : ℕ) (hn : 0 < n) (M G : ZMat n)
    (hM : Unimodular M) (hG : G = M.transpose * M) (a : ZVec n) :
    ((screen G a).isSome ↔ supportSize (M.mulVec a) = 1) ∧
    (∀ a₀, screen G a = some a₀ → UnitAnswer G a₀) := by sorry
end ZLIPPadding.Padding
