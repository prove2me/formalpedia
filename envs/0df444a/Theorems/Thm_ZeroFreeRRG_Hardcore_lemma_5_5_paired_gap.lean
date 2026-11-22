-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_paired_gap
-- name    : ZeroFreeRRG.Hardcore.lemma_5_5_paired_gap
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:52:40.116982+00:00
-- url     : https://prove2.me/theorems/b06ee313-2da6-434d-a3e8-557ff8e98177
-- title:
--   Lemma 5.5(2) — local paired Bethe quadratic gap
-- statement:
--   Under the standing assumptions of Lemma 5.5, every sufficiently small open overlap box $B$ around $\pi(t)\otimes\pi(t)$ admits $c>0$ and a parameter disk $D_0$ such that, for real $s,u\in D_0$ with nonnegative edge matrices $P(s),P(u)$ and for every edge marginal $Q$ with vertex marginal $\rho\in B$,
--
--   $$\Phi_{s,u}(\rho,Q)\le -c\left(\|\rho-\pi(s)\otimes\pi(u)\|_2^2+\|Q-P(s)\otimes P(u)\|_F^2\right).$$
--
--   Here $\Phi_{s,u}=(d-1)D_{\mathrm{KL}}(\rho\|\pi(s)\otimes\pi(u))-\frac d2D_{\mathrm{KL}}(Q\|P(s)\otimes P(u))$.
--
--   This is Lemma 5.5(2). Lemma D.1 supplies the tilted optimizer $Q^*$ and the positive-definite Hessian of the reduced profile rate function; Lemma D.2 combines its Taylor expansion with Pinsker’s inequality to produce the displayed quadratic gap on the paired alphabet.
--
--   **Formalization Note.** The rate function is `EReal`-valued, so the bound also covers its $-\infty$ case.
-- source:
--   Chen, Wang, Zhang, arXiv:2610.40510 (held version), Lemma 5.5(2), printed p. 40; proof via Lemmas D.1 and D.2 in Appendix D.1–D.2 and D.3, printed pp. 68–71.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- Lemma 5.5(2): the paired Bethe rate function has a local negative quadratic upper bound. -/
theorem lemma_5_5_paired_gap (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧
        (∀ s u : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (u : ℂ) ∈ Metric.ball (t : ℂ) R →
          (∀ i j, 0 ≤ m.P s i j) → (∀ i j, 0 ≤ m.P u i j) →
          ∀ (ρ : m.Spin × m.Spin → ℝ) (Q : m.Spin × m.Spin → m.Spin × m.Spin → ℝ),
            IsEdgeMarginal ρ Q → ρ ∈ overlapBox c₀ lo hi →
            rateFn d (tensorVec (m.pi s) (m.pi u)) (tensorMat (m.P s) (m.P u)) ρ Q ≤
              (((-c) * sqDist ρ (tensorVec (m.pi s) (m.pi u)) Q (tensorMat (m.P s) (m.P u)) : ℝ)
                : EReal)) := by sorry
