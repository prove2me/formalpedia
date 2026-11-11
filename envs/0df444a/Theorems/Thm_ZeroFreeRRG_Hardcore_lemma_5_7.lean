-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_7
-- name    : ZeroFreeRRG.Hardcore.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:37:44.281185+00:00
-- url     : https://prove2.me/theorems/c9d9b6dd-69eb-4c34-aa7e-a4646dd10ce9
-- title:
--   Lemma 5.7 — max degree ≤ d: no hardcore zeros for |λ| < (d−1)^{d−1}/d^d, no Potts zeros for |β − 1| < 0.35/d
-- statement:
--   For every simple graph $G$ of maximum degree at most $d$, the hardcore partition function $Z_{G,\mathrm{fug}}(\lambda)$ has no zero in
--   $$|\lambda|<\frac{(d-1)^{d-1}}{d^d}$$
--   (Shearer's bound), and for every $q\ge2$ the Potts partition function $Z_{G,q}(\beta)$ has no zero in $|\beta-1|<0.35/d$. It covers the independent-spin endpoints $\alpha=0$ and $\beta=1$ in Theorem 5.1.
--
--   Differences from the source:
--   - reading: d (maximum degree) → 3 ≤ d; reason: §2.4 standing convention 'We use d ≥ 3 for an integer regular degree'; the lemma is applied with that d
--   - encoding: every simple graph G of maximum degree at most d → every SimpleGraph on a finite type V : Type with degree v ≤ d for all v; reason: finite vertex sets; Type 0 suffices for graphs
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 40, Lemma 5.7 (cited from [She85, SS05, BS17])

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Models

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 5.7** (deterministic zero-freeness near trivial endpoints; p. 40). For every simple
graph `G` of maximum degree at most `d`, the hardcore partition function `Z_{G,fug}(λ)` has no zero
with `|λ| < (d − 1)^{d−1}/d^d`, and for every `q ≥ 2` the Potts partition function `Z_{G,q}(β)` has
no zero with `|β − 1| < 0.35/d`. -/
theorem lemma_5_7 (d : ℕ) (hd : 3 ≤ d) :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ d) →
      ∀ lam : ℂ, ‖lam‖ < ((d : ℝ) - 1) ^ (d - 1) / (d : ℝ) ^ d → hardcoreZfug G lam ≠ 0) ∧
    (∀ q : ℕ, 2 ≤ q → ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ d) →
      ∀ β : ℂ, ‖β - 1‖ < 0.35 / (d : ℝ) → pottsZ q G β ≠ 0) := by sorry

end ZeroFreeRRG.Hardcore
