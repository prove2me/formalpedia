-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_cycle_moments
-- name    : ZeroFreeRRG.Hardcore.lemma_5_5_cycle_moments
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:06.778968+00:00
-- url     : https://prove2.me/theorems/f5c0bf61-bb6c-4b94-803b-c4fcefbf0c6f
-- title:
--   Lemma 5.5(3) — Poisson short cycles and weighted factorial moments
-- statement:
--   Under the assumptions of Lemma 5.5, for every sufficiently small overlap box $B$ about $\pi(t)\otimes\pi(t)$ there is a real-parameter neighbourhood $D_0$ with the following properties. For every $k\ge1$, the cycle counts satisfy
--
--   $$(X_{1,n},\ldots,X_{k,n})\xrightarrow{d}(Z_1,\ldots,Z_k),$$
--
--   where the $Z_\ell$ are independent Poisson variables with means $\lambda_\ell=(d-1)^\ell/(2\ell)$. For real $s\in D_0$ with $P(s)\ge0$ and every choice of $j_1,\ldots,j_k\ge0$, equation (39) holds:
--
--   $$\frac{E[\mathcal Z^{(2)}_{G,B}(s,s)]}{a_n(s)^2}\longrightarrow\exp\left(\sum_{\ell\ge1}\lambda_\ell\delta_\ell(s)^2\right),$$
--
--   $$\frac{E[\mathcal Z_G(s)\prod_{\ell=1}^k(X_{\ell,n})_{j_\ell}]}{a_n(s)}\longrightarrow\prod_{\ell=1}^k[\lambda_\ell(1+\delta_\ell(s))]^{j_\ell},$$
--
--   where $(x)_j=x(x-1)\cdots(x-j+1)$.
--
--   The unweighted statement is the configuration-model factorial-moment computation in Appendix D.3. The weighted statement follows by working under the planted law, averaging conditional trace factors over profiles concentrated by Proposition 5.3. The second-moment limit is the real specialization of the determinant limit from Lemma D.3 through the trace identity $\delta_\ell(s)=\operatorname{tr}R_s^\ell$.
--
--   **Formalization Note.** For point probabilities, the product of Poisson masses is the limit law for the $\mathbb N^k$-valued cycle vector; factorial powers use `Nat.descFactorial`.
-- source:
--   Chen, Wang, Zhang, arXiv:2610.40510 (held version), Lemma 5.5(3) and equation (39), printed p. 40; proof in Appendix D.3, printed pp. 71–73, with the paired determinant limit from Lemma D.3, printed pp. 69–70.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- Lemma 5.5(3): joint Poisson convergence of short cycles and the two limits in equation (39). -/
theorem lemma_5_5_cycle_moments (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ R : ℝ, 0 < R ∧
        (∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
          Tendsto (fun n => cmProb (fun M : Matching n d => ∀ i : Fin k, cycleCount M ((i : ℕ) + 1) = j i))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (∏ i : Fin k, (ProbabilityTheory.poissonMeasure (lamCyc d ((i : ℕ) + 1)).toNNReal).real {j i}))) ∧
        (∀ s : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (∀ i j, 0 ≤ m.P s i j) →
          Tendsto (fun n => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) s s M) /
              an m d n (s : ℂ) ^ 2)
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (Complex.exp (∑' ℓ : ℕ, (lamCyc d (ℓ + 1) : ℂ) * deltaCyc m (ℓ + 1) s ^ 2))) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
            Tendsto (fun n => cmE (fun M : Matching n d => normZ m (s : ℂ) M *
                ∏ i : Fin k, (((cycleCount M ((i : ℕ) + 1)).descFactorial (j i) : ℕ) : ℂ)) /
                an m d n (s : ℂ))
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (𝓝 (∏ i : Fin k, ((lamCyc d ((i : ℕ) + 1) : ℂ) * (1 + deltaCyc m ((i : ℕ) + 1) s)) ^ (j i)))) := by sorry
