-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_even_power_finite_extractions_below_raw
-- name    : mme_CW_q6_coupled_even_power_finite_extractions_below_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:11:53.173824+00:00
-- url     : https://prove2.me/theorems/285642a9-b29c-4c3e-a842-83c687322cc8
-- title:
--   Even-power coupled extraction at every base below the $q=6$ raw value
-- statement:
--   Fix $\tau$ with $3\tau\ge2$, let $D_6$ be the explicit four-sum coupled Coppersmith--Winograd constituent, and choose a nonnegative real number
--
--   $$
--   0\le V< R(\tau):=4\,6^{3\tau}(6^{3\tau}+2).
--   $$
--
--   For every sufficiently large $N$, set
--
--   $$
--   \lambda=\frac{2}{6^{3\tau}+2},\qquad L=\lfloor\lambda N\rfloor,\qquad G=N-L.
--   $$
--
--   Then $L>0$, $L+G=N$, and the exact pruning condition $341L<100G$ holds. Moreover there is a finite family of matrix-multiplication tensors with a concrete modewise restriction
--
--   $$
--   \bigoplus_i\langle a_{N,i},b_{N,i},c_{N,i}\rangle
--   \;\leq_{\mathrm{Restrict}}\;
--   \bigl(D_6\otimes\pi(D_6)\otimes\pi^2(D_6)\bigr)^{\otimes 2N}
--   $$
--
--   whose weighted volume satisfies
--
--   $$
--   V^{2N}\le\sum_i(a_{N,i}b_{N,i}c_{N,i})^{\tau}.
--   $$
--
--   The strict inequality $V<R(\tau)$ is essential: it absorbs the Stirling and Salem--Spencer subexponential losses in the proof on journal pp. 270--272. Thus the statement records exactly the exponential-rate conclusion of the paper without asserting constant-relative attainment at the boundary value. It retains the literal even power, rounded type counts, pruning certificate, direct sum, and actual tensor-restriction witnesses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), proof of the coupled-constituent lemma on journal pp. 270--272 (PDF pp. 20--22), including the 2N-th power, L/G optimization, Salem--Spencer hashing, collision pruning, and nth-root value estimate; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
open MME BigOperators Filter
universe u

theorem mme_CW_q6_coupled_even_power_finite_extractions_below_raw
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      0 < L ∧ L + G = N ∧ 341 * L < 100 * G ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
