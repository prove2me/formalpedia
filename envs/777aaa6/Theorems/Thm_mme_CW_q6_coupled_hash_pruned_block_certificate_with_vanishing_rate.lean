-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
-- name    : mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:47:49.233949+00:00
-- url     : https://prove2.me/theorems/e6e33020-c2ae-4735-816c-a184af3de9a2
-- title:
--   Coupled $q=6$ hash-pruning certificate with an explicit vanishing root loss
-- statement:
--   Fix a field $K$ and $\tau$ with $3\tau\ge 2$. For the coupled Coppersmith--Winograd constituent at $q=6$, there is a nonnegative loss sequence $\delta_N\to0$ such that the $2N$-th power of its cyclic symmetrization restricts to a genuinely mode-disjoint graded family of fine-structure survivors. With
--
--   $$
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad G=N-L,\qquad s=36^{2G}6^{2L},
--   $$
--
--   and raw cyclic base $R=4\,6^{3\tau}(6^{3\tau}+2)$, the surviving address set $C$ satisfies
--
--   $$
--   \bigl(R e^{-\delta_N}\bigr)^{2N}\le |C|\,(s^3)^\tau.
--   $$
--
--   The tensor $P$ is an actual coordinate restriction of the source power. Its retained block addresses differ in every mode, all non-retained blocks vanish, and each retained block restricts to the concrete survivor $S_{L,G}$. Thus the statement records direct-sum compatibility rather than counting triples that still share a $Z$-block. The vanishing loss simultaneously records the Behrend density, collision pruning, and multinomial/Stirling factors; it is an exponential-rate statement and makes no false endpoint-attainment claim.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), proof of the coupled-constituent lemma on journal pp. 270--272 (PDF pp. 20--22), especially the 2N-th power, L/G profile, modulus M, Salem--Spencer hashing, shared-X/Y pruning, C-tensor multiplicity H, and the displayed auxiliary estimate on p. 271; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter Topology
universe u

theorem mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ rate : ℕ → ℝ,
      (∀ N, 0 ≤ rate N) ∧
      Tendsto rate atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let Gcount : ℕ := N - L
        let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
        ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
            (C : Finset (Fin 3 → Fin t))
            (σs : Fin C.card → (Fin 3 → Fin t)),
          TensorObj.Restrict P
              ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (∀ j, σs j ∈ C) ∧
          Function.Injective σs ∧
          (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
            ∀ i : Fin 3, σ i ≠ σ' i) ∧
          (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
          (∀ j, TensorObj.Restrict
            (coupledQ6Survivor K L Gcount)
            (grading.blockSubtensor (σs j))) ∧
          (raw * Real.exp (-rate N)) ^ (2 * N) ≤
            (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by sorry
