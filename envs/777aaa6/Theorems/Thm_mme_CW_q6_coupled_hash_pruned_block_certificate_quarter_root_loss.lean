-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss
-- name    : mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:56:42.751119+00:00
-- url     : https://prove2.me/theorems/c2024eb4-b77f-4114-bf8d-05e286d024a0
-- title:
--   Coupled $q=6$ hash-pruning certificate with a concrete fourth-root loss
-- statement:
--   Fix a field $K$ and $\tau$ with $3\tau\ge 2$. In the coupled Coppersmith--Winograd construction at $q=6$, set
--
--   $$
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad G=N-L,\qquad s=36^{2G}6^{2L},
--   $$
--
--   and assume the source profile conditions $L>0$, $L+G=N$, and $341L<100G$. For all sufficiently large $N$, the $2N$-th power of the cyclic symmetrization has a coordinate restriction whose nonzero graded blocks form a mode-disjoint family $C$ of concrete coupled survivors $S_{L,G}$. If $R=4\,6^{3\tau}(6^{3\tau}+2)$ and $\delta_N=(N+1)^{-1/4}$, then
--
--   $$
--   \bigl(R e^{-\delta_N}\bigr)^{2N}\le |C|\,(s^3)^\tau.
--   $$
--
--   The statement requires actual tensor restriction and mode-disjoint block addresses: all blocks outside $C$ vanish and each block in $C$ restricts to $S_{L,G}$. In particular, the $H$ middle-index choices inside a C-tensor are not declared to be an exact direct sum merely because they have distinct $X$- and $Y$-supports but share a $Z$-block. The count instead includes both progression-free-set losses: the first removes collisions among the coarse coupled constituents, while a second induced-matching extraction converts the cyclic macro tensor of type $\langle H,H,H\rangle$ into $H^{2-o(1)}$ mode-disjoint fine survivors. The concrete fourth-root discount is deliberately weaker than these $O(N^{-1/2})$ per-root Behrend losses and also absorbs polynomial Stirling, floor, and fixed-constant factors. No exact $H^2$ diagonalization or endpoint attainment is asserted.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--272 (PDF pp. 20--22): the coupled constituent's 2N-th power, the L/G profile, Salem--Spencer hashing, C-tensor multiplicity H, cyclic macro matrix-multiplication tensor, and its progression-free induced-matching extraction; https://www.sciencedirect.com/science/article/pii/S0747717108800132. The explicit finite progression-free witness is supplied by mme_behrend_explicit_threeAP_free (Prove2Me theorem cb45e6ba-b86a-4119-a08e-f162c8fbc86b), formalizing Behrend's lower bound.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter Topology
universe u

theorem mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
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
        (raw * Real.exp (-loss)) ^ (2 * N) ≤
          (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by sorry
