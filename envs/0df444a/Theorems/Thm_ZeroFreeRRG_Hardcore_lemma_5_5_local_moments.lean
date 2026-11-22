-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_local_moments
-- name    : ZeroFreeRRG.Hardcore.lemma_5_5_local_moments
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:51:59.808802+00:00
-- url     : https://prove2.me/theorems/f1e857fa-1c99-4bba-a04a-f489dc438c7b
-- title:
--   Lemma 5.5(1) — holomorphic local first- and second-moment limits
-- statement:
--   Fix a hardcore or Potts model, $d\ge3$, and a nontrivial real parameter $t$ whose nonconstant kernel eigenvalues are nonpositive and which satisfies the strict Kesten–Stigum Condition 2. There is a threshold $r>0$ such that for every open overlap box $B$ about $\pi(t)\otimes\pi(t)$ with all side lengths below $r$, there is a disk $D_0$ about $t$ on which
--
--   $$a_n(z)=E_{\mathrm{CM}_{n,d}}[\mathcal Z_G(z)]\longrightarrow A(z)$$
--
--   locally uniformly, with $A$ holomorphic and nowhere zero, and
--
--   $$\frac{E_{\mathrm{CM}_{n,d}}[\mathcal Z^{(2)}_{G,B}(z,w)]}{a_n(z)a_n(w)}\longrightarrow G_2(z,w)$$
--
--   locally uniformly on $D_0\times D_0$, with $G_2$ holomorphic.
--
--   This is Lemma 5.5(1). In Appendix D it follows by truncating profiles away from a small density box using Proposition 5.3, then applying the coefficient-extraction and Laplace asymptotics of Lemma D.3 to the first-moment and paired models.
--
--   **Formalization Note.** Convergence is along positive admissible sizes, encoded by the filter $n\to\infty$ restricted to $dn$ even; the disk is `Metric.ball (t : ℂ) R`.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version), Lemma 5.5(1), printed p. 40; proof in Appendix D.3, printed pp. 70–72, using Lemma D.3 (printed pp. 69–70) and Proposition 5.3 (printed p. 39).

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- Lemma 5.5(1): local first and second moments have holomorphic locally uniform limits. -/
theorem lemma_5_5_local_moments (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ R : ℝ, 0 < R ∧
        (∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (t : ℂ) R) ∧
            (∀ z ∈ Metric.ball (t : ℂ) R, A z ≠ 0) ∧
            TendstoLocallyUniformlyOn (fun n z => an m d n z) A
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (Metric.ball (t : ℂ) R)) ∧
        (∃ G2 : ℂ × ℂ → ℂ,
            DifferentiableOn ℂ G2 (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R) ∧
            TendstoLocallyUniformlyOn
              (fun n (p : ℂ × ℂ) => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) p.1 p.2 M) /
                (an m d n p.1 * an m d n p.2)) G2
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R)) := by sorry
