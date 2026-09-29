-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
-- name    : mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T05:47:58.666994+00:00
-- url     : https://prove2.me/theorems/d8b31bfb-bcd6-4fed-bd9e-b0884e1d12bf
-- title:
--   Finite pruned-block certificate for the q=6 coupled CW extraction below the raw base
-- statement:
--   This is the finite certificate produced by the coupled Coppersmith--Winograd hashing and pruning argument for q=6. For every nonnegative V strictly below the raw base 4*6^(3*tau)*(6^(3*tau)+2), and for all sufficiently large even-power parameters N satisfying the exact floor profile L=floor(2N/(6^(3*tau)+2)), G=N-L and 341L<100G, it returns an actual pruned tensor P obtained by restriction from the 2N-th power of the cyclic coupled tensor.
--
--   The certificate equips P with a finite mode grading and enumerates a set C of retained block addresses. The addresses are injectively enumerated and any two distinct retained addresses differ in every mode; every block outside C is zero. Each retained block restricts to the concrete tensor coupledQ6Survivor K L G, and the cardinality of C obeys the exact below-base weighted inequality
--
--   $$V^{2N} \le |C|\,\bigl((36^{2G}6^{2L})^3\bigr)^\tau.$$
--
--   The proved generic independent-block theorem can therefore turn this certificate into a restriction to a direct sum of the survivor tensors. The strict inequality V<4*6^(3*tau)*(6^(3*tau)+2) absorbs the subexponential Stirling and Salem--Spencer density losses without asserting false relative-error attainment at the limiting base.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), proof of the coupled-constituent lemma on journal pp. 270--272 (PDF pp. 20--22): 2N-th power, exact L/G profile, Salem--Spencer hashing, shared-X/Y collision pruning, C-tensor blocks, and the finite value estimate; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_salem_spencer_eps_form
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter
universe u

theorem mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
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
        V ^ (2 * N) ≤
          (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by sorry
