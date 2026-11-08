-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_19_integral
-- name    : ZeroExtensionGap.lemma_19_integral
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:15.6592+00:00
-- url     : https://prove2.me/theorems/2c366318-0727-4b1f-9980-bc37b78fd509
-- title:
--   Lemma 19 — every integral assignment has cost at least $c_tN\rho$
-- statement:
--   There is a constant $c_t>0$ such that, for every sufficiently large even integer $n$, every integral assignment for the instance $I$ constructed in Section 4.1 has cost at least
--
--   $$c_tN\rho=c_tN(\log n)^{(t-1)/(t+1)}.$$
--
--   This is the lower half of the integrality gap, for every valid tower and every retraction of $I$.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: $V=V(X)\cup T$ and $D(x_T,y_T)=d_X(x,y)$ → vertex type `V(X) ⊕ V(X)` (`Sum.inl` for $X$, `Sum.inr` for terminals) and `D` the real value of the `ℝ≥0∞` distance of $X$ (`gapInstance`); reason: on a valid tower $X$ is connected, so the distance is finite and its real value is $d_X$
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 19, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_ZeroExtensionGap_gapInstance

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 19, p.28 (PDF p.30).
**Formalization Note.** An integral assignment is a retraction of the instance of §4.1, with its cost. The bound
holds for all retractions and every valid tower; `N = n^t` and `ρ = (log n)^{(t-1)/(t+1)}`. `c_t` and `N₀` depend on
`t` and the constants of Lemmas 2 and 7 only. -/
theorem lemma_19_integral (t : ℕ) (ht : 2 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ ct : ℝ, 0 < ct ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
      ∀ f, (gapInstance t H (gOf γ n) φ).IsRetraction f →
        ct * (n : ℝ) ^ t * rho t n ≤ (gapInstance t H (gOf γ n) φ).cost f := by sorry

end ZeroExtensionGap
