-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_9
-- name    : Z2PostSamp.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:51.467501+00:00
-- url     : https://prove2.me/theorems/4e6f9ca8-d526-4f38-b718-5e5b3254bb27
-- title:
--   Lemma 3.9 — cavity Gaussian estimate: $\sup_{|s|\le1}\mathbb E|D_i(s)|^2\le C_\lambda N/n^2$
-- statement:
--   Fix $\lambda>1$, $k\ge k_0$, a free site $i\in R_k$, and put $N=n-k-1\ge1$. With the cavity average $\langle\cdot\rangle_{-i}$ (site $i$ deleted, fields $h^{(k)}_j(\theta_{S_k})$ retained) and
--
--   $$Y_i(\sigma)=\sum_{j\in R_k\setminus\{i\}}J_{ij}(\sigma_j-m^{-i}_j),\quad v_i=\frac{\lambda^2}n(N-\|m^{-i}\|^2),\quad\mathcal Z_i(s)=\langle e^{sY_i(\sigma)}\rangle_{-i},\quad D_i(s)=\frac{\mathcal Z_i'(s)}{\mathcal Z_i(s)}-sv_i,$$
--
--   there is a constant $C_\lambda$ (independent of $n$, $k$ and $i$) such that
--
--   $$\sup_{|s|\le1}\mathbb E|D_i(s)|^2\le\frac{C_\lambda N}{n^2}.\tag{3.20}$$
--
--   Since $\langle Y_i\rangle_{-i}=0$, Jensen gives $\mathcal Z_i\ge1$; the lemma says the cavity field is nearly Gaussian with variance $v_i$, which yields the TAP gradient residual of Lemma 3.8.
--
--   **Formalization Note** The free site is $i=I_{a+1}$ for any position $a\ge k$ of the order, so every free site is covered. The expectation is the lower Lebesgue integral under the planted law; the supremum is the bound for every $s\in[-1,1]$; $\mathcal Z_i'(s)$ is written as $\langle Y_ie^{sY_i}\rangle_{-i}$.
--
--   Differences from the source:
--   - reading: a fixed free site i ∈ R_k → i = I_{a+1} for every position a with k ≤ a < n; reason: R_k is random (it depends on I); indexing the free site by its position in the order covers every free site
--   - encoding: sup_{|s|≤1} E|D_i(s)|² → the bound for every s ∈ [−1, 1]; reason: definition of the supremum bound
--   - reading: Fix k … N = n − k − 1, initially assuming N ≥ 1 → k₀ ≤ k and k + 2 ≤ n; reason: §3.5 serves Lemma 3.8, whose range is k₀ ≤ k < n; the case N = 0 is treated separately on p.31 (empty cavity sums, D_i = 0)
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.9, p.29, (3.20); definitions §3.5, p.29

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Cavity

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 3.9 (cavity Gaussian estimate).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §3.5, p.29: "Fix `k` and a free site `i ∈ R_k`. … put `N = n − k − 1`, initially assuming
`N ≥ 1`. … Define, for `−1 ≤ s ≤ 1`, `Y_i(σ) = Σ_{j∈R_k∖{i}} J_ij(σ_j − m^{−i}_j)`,
`v_i = (λ²/n)(N − ‖m^{−i}‖²)`, `𝒵_i(s) = ⟨e^{sY_i(σ)}⟩_{−i}`, `D_i(s) = 𝒵_i'(s)/𝒵_i(s) − s v_i`."
Lemma 3.9: "We have `sup_{|s|≤1} E|D_i(s)|² ≤ C_λ N/n²` (3.20)."

**Formalization Note.** `λ > 1` is fixed and `k₀ ≤ k` (the range of §3.5). The free site is
`i = I_{a+1}` for any position `a ≥ k` of the order (every free site arises so), the expectation is the
lower Lebesgue integral under the planted law with the retained fields `h^{(k)}(θ_{S_k})`. The `sup`
over `|s| ≤ 1` is the bound for every such `s`. `N = n − k − 1 ≥ 1` is `k + 2 ≤ n`. -/
theorem lemma_3_9 (lam : ℝ) (hlam : 1 < lam) :
    ∃ C : ℝ, ∀ n k : ℕ, k0 n lam ≤ k → k + 2 ≤ n → ∀ a : Fin n, k ≤ a.val →
      ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
        ∫⁻ ω, ENNReal.ofReal (cavD lam (Jof n lam ω) ω.2.2 ω.1 k (ω.2.2 a) s ^ 2) ∂(plantedLaw n)
          ≤ ENNReal.ofReal (C * ((n : ℝ) - k - 1) / (n : ℝ) ^ 2) := by sorry

end Z2PostSamp
