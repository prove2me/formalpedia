-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_10_fractional
-- name    : ZeroExtensionGap.lemma_10_fractional
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:45.679559+00:00
-- url     : https://prove2.me/theorems/0c8c4f0d-4ef9-4aed-ba79-8d1933242a56
-- title:
--   Lemma 10 — the fractional solution: $\mathrm{EM}(I)\le(\eta+10t)N$
-- statement:
--   The instance $I$ constructed in Section 4.1 from a valid expander tower satisfies
--
--   $$\mathrm{EM}(I)\le(\eta+10t)N,$$
--
--   where $N=n^t$ and $\eta=50/h_0$. This is the upper half of the integrality gap.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: $V=V(X)\cup T$ and $D(x_T,y_T)=d_X(x,y)$ → vertex type `V(X) ⊕ V(X)` (`Sum.inl` for $X$, `Sum.inr` for terminals) and `D` the real value of the `ℝ≥0∞` distance of $X$ (`gapInstance`); reason: on a valid tower $X$ is connected, so the distance is finite and its real value is $d_X$
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 10, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ZeroExtensionGap_gapInstance

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 10, p.20 (PDF p.22).
**Formalization Note.** `t ≥ 2` and `n` sufficiently large and even are the standing assumptions of §4.1,
p.19 (PDF p.21); `N = n^t` and `η = 50/h₀`. The statement holds for every valid tower. -/
theorem lemma_10_fractional (t : ℕ) (ht : 2 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
        (gapInstance t H (gOf γ n) φ).EM ≤ (eta h₀ + 10 * (t : ℝ)) * (n : ℝ) ^ t := by sorry

end ZeroExtensionGap
