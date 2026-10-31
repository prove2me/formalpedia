-- Prove2me | Theorems.Thm_ZeroOneSCO_eq_9
-- name    : ZeroOneSCO.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:04.928765+00:00
-- url     : https://prove2.me/theorems/0903337a-a14a-452d-b1e1-a67d8f6f7d3f
-- title:
--   Display (9): $Z^{\downarrow}_s$ vanishes exactly when $\|Z\|_0^+<s$
-- statement:
--   Let $Z\in\mathbb R^{M\times N}$ and let $s\ge1$ be an integer. Let $Z^{\downarrow}_r$ be the $r$th largest element of $\{\|(Z_{:1})^+\|,\dots,\|(Z_{:N})^+\|\}$. Then
--   $$
--   Z^{\downarrow}_s=0\ \text{ if }\ \|Z\|_0^+<s,\qquad Z^{\downarrow}_s>0\ \text{ if }\ \|Z\|_0^+\ge s.
--   $$
--   This fact makes the threshold $\tau_*$ positive and separates the two cases of the stationarity conditions.
--
--   Differences from the source:
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - encoding: Z↓_s, undefined on the page when s > N → rthLargest has value 0 when s > N; reason: then ‖Z‖₀⁺ ≤ N < s, and 0 is the value (9) prescribes
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, (9), p.5

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace ZeroOneSCO

/-- Display (9), Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.5: `Z↓_s = 0` if `‖Z‖₀⁺ < s`, and
`Z↓_s > 0` if `‖Z‖₀⁺ ≥ s`.

**Formalization Note.** `s` is the paper's positive integer (p.3), and `Z↓_s` is `0` when `s > N`
(`rthLargest`). -/
theorem eq_9 {M N : ℕ} [NeZero M] (Z : Mat M N) (s : ℕ) (hs : 0 < s) :
    (plusZero Z < s → rthLargest Z s = 0) ∧ (s ≤ plusZero Z → 0 < rthLargest Z s) := by sorry

end ZeroOneSCO
