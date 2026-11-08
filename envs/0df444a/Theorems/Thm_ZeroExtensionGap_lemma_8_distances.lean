-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_8_distances
-- name    : ZeroExtensionGap.lemma_8_distances
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:33.854217+00:00
-- url     : https://prove2.me/theorems/55a4fcb5-f9b3-4149-a9f5-7232d61cff99
-- title:
--   Lemma 8 — distances between stages of a valid tower
-- statement:
--   Let $X_t,\dots,X_1$ be a valid expander tower with final graph $X=X_1$. For every $i\in[t-1]$ and $x,y\in V(X_i)$,
--
--   $$d_{X_{i+1}}(p_i(x),p_i(y))\le d_{X_i}(x,y)\le d_{X_{i+1}}(p_i(x),p_i(y))+2\eta\sigma_i.$$
--
--   Consequently, for every $r\in[t]$ and $x,y\in V(X)$,
--
--   $$d_{X_r}(\pi_r(x),\pi_r(y))\le d_X(x,y)\le d_{X_r}(\pi_r(x),\pi_r(y))+2\eta\sum_{i=1}^{r-1}\sigma_i.$$
--
--   In particular, $\max_{x,y\in V(X)}d_X(x,y)\le(2t-1)\eta\sigma_t$.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: shortest-path distance $d$ with values in $[0,\infty]$ → `ℝ≥0∞`, with `toReal` under connectivity; reason: on connected pairs the real value is the distance; there is no junk value
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 8, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 8, p.17 (PDF p.19): the distance comparison between consecutive stages, its consequence
for `π_r`, and the bound on the diameter of `X`.
**Formalization Note.** Depth `j` is `X_{i+1}` and depth `j + 1` is `X_i`, with `i = t - (j + 1)`; `p_i` is
the first component. Distances are in `ℝ≥0∞`, so no connectivity guard is needed. `n` sufficiently large
and even is standing (§3, p.11, PDF p.13). For `r = 1` the sum is empty. -/
theorem lemma_8_distances (t : ℕ) (ht : 1 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
        (∀ j, j + 1 < t → ∀ x y : TowerV n (j + 1),
          towerDist t H (gOf γ n) φ j x.1 y.1 ≤ towerDist t H (gOf γ n) φ (j + 1) x y ∧
          towerDist t H (gOf γ n) φ (j + 1) x y ≤ towerDist t H (gOf γ n) φ j x.1 y.1 +
            ENNReal.ofReal (2 * eta h₀ * sigma t n (t - (j + 1)))) ∧
        (∀ (r : ℕ) (hr : 1 ≤ r), r ≤ t → ∀ x y : TowerV n (t - 1),
          towerDist t H (gOf γ n) φ (t - r) (piProj t r hr x) (piProj t r hr y) ≤
            towerDist t H (gOf γ n) φ (t - 1) x y ∧
          towerDist t H (gOf γ n) φ (t - 1) x y ≤
            towerDist t H (gOf γ n) φ (t - r) (piProj t r hr x) (piProj t r hr y) +
              ENNReal.ofReal (2 * eta h₀ * ∑ i ∈ Finset.Icc 1 (r - 1), sigma t n i)) ∧
        (∀ x y : TowerV n (t - 1), towerDist t H (gOf γ n) φ (t - 1) x y ≤
          ENNReal.ofReal ((2 * (t : ℝ) - 1) * eta h₀ * sigma t n t)) := by sorry

end ZeroExtensionGap
