-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_eq4_gap_le_cell_deviation
-- name    : XuMannorRobust.Standard.eq4_gap_le_cell_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:37:04.540285+00:00
-- url     : https://prove2.me/theorems/a84c216a-ffa3-4197-b216-c140f73dcaa7
-- title:
--   Eq. (4): $|\mathcal L(\mathcal A_s) - l_{\mathrm{emp}}(\mathcal A_s)| \le \epsilon(s) + M\sum_i ||N_i|/n - \mu(C_i)|$
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$, and let $l : \mathcal H \times \mathcal Z \to \mathbb R$ be a loss with $0 \le l(h,z) \le M$ for all $h, z$ and $l(h,\cdot)$ measurable for every $h$. Let $n \ge 1$, let $\mathcal A : \mathcal Z^n \to \mathcal H$ be a learning algorithm and $\epsilon(\cdot) : \mathcal Z^n \to \mathbb R$, and let $C_1, \dots, C_K$ be a partition of $\mathcal Z$ into pairwise disjoint measurable sets such that, for every training set $\mathbf s$, every training point $s_j$, every $z \in \mathcal Z$ and every $i$,
--
--   $$s_j, z \in C_i \implies |l(\mathcal A_{\mathbf s}, s_j) - l(\mathcal A_{\mathbf s}, z)| \le \epsilon(\mathbf s)$$
--
--   (condition (2) of Definition 2). Then for **every** training set $\mathbf s \in \mathcal Z^n$, with $|N_i|$ the number of training points in $C_i$,
--
--   $$|\mathcal L(\mathcal A_{\mathbf s}) - l_{\mathrm{emp}}(\mathcal A_{\mathbf s})| \le \epsilon(\mathbf s) + M \sum_{i=1}^K \left| \frac{|N_i|}{n} - \mu(C_i) \right|.$$
--
--   This is Eq. (4), the deterministic half of the proof of Theorem 1: it reduces the generalization gap of a robust algorithm to the deviation of the empirical cell frequencies from the true cell probabilities.
--
--   **Formalization Note** Measurability of $l(h,\cdot)$ and of the cells is added to the paper's standing assumptions (which ignore measurability); with the bound $0 \le l \le M$ it makes $l(h,\cdot)$ integrable, so $\mathcal L$ is the true expectation. The statement is the last line (4) of the paper's chain, which avoids conditional expectations on cells of measure zero. The partition is named explicitly rather than through Definition 2's existential.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 397, proof of Theorem 1, Eq. (4)

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_CellCount

open MeasureTheory

namespace XuMannorRobust.Standard

/-- **Eq. (4)** (Xu & Mannor 2012, p. 397, proof of Theorem 1). Let the loss take values in
`[0, M]` with `l h` measurable for every `h`, let `μ` be a probability measure, and let the
measurable partition `C_1, …, C_K` of `Z` witness condition (2) of Definition 2 for the algorithm
`A` with `ε(·)`. Then for every training set `s` of size `n ≥ 1` (deterministically),
`|𝓛(A_s) − l_emp(A_s)| ≤ ε(s) + M ∑_i ||N_i|/n − μ(C_i)|`. -/
theorem eq4_gap_le_cell_deviation {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ) (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) {K : ℕ}
    (ε : (Fin n → Z) → ℝ) (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    (hC_robust : ∀ s : Fin n → Z, ∀ j : Fin n, ∀ z : Z, ∀ i : Fin K,
      s j ∈ C i → z ∈ C i → |l (A s) (s j) - l (A s) z| ≤ ε s) :
    ∀ s : Fin n → Z,
      |expectedLoss μ l (A s) - empiricalLoss l (A s) s|
        ≤ ε s + M * ∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal| := by sorry

end XuMannorRobust.Standard
