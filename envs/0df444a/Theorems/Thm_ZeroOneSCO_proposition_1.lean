-- Prove2me | Theorems.Thm_ZeroOneSCO_proposition_1
-- name    : ZeroOneSCO.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:13.52826+00:00
-- url     : https://prove2.me/theorems/8691308f-0176-4648-a824-357eddb82300
-- title:
--   Proposition 1: closed form of the projection onto $\mathcal S$
-- statement:
--   For $Z\in\mathbb R^{M\times N}$ and an integer $s\ge1$,
--   $$
--   \Pi_{\mathcal S}(Z)=\Bigl\{\bigl[(Z_{:T})^-\ \ Z_{:\overline T}\bigr]:\ T\in\mathbb T(Z;s)\Bigr\}.
--   $$
--   So every nearest point of $\mathcal S$ keeps $s$ columns of largest positive part and replaces the positive part of every other column by zero. This is the formula on which the stationarity conditions and the index-set selection of the algorithm rest.
--
--   Differences from the source:
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - encoding: the block matrix [(Z_{:T})⁻ Z_{:T̄}] and argmin of ‖Z − Y‖ → glue T Z, defined entrywise, and projS minimizing the squared Frobenius norm; reason: the same matrix with no column permutation, and the same minimizers
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Proposition 1, (21), p.7

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace ZeroOneSCO

/-- Proposition 1, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, (21), p.7:
`Π_S(Z) = {[(Z_{:T})⁻ Z_{:T̄}] : T ∈ 𝕋(Z; s)}`. -/
theorem proposition_1 {M N : ℕ} [NeZero M] (Z : Mat M N) (s : ℕ) (hs : 0 < s) :
    projS s Z = {Y | ∃ T ∈ TSet Z s, Y = glue T Z} := by sorry

end ZeroOneSCO
