-- Prove2me | Theorems.Thm_mme_canonical_square_piece_restricts_restrictedPower
-- name    : mme_canonical_square_piece_restricts_restrictedPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T09:47:20.310695+00:00
-- url     : https://prove2.me/theorems/1323c239-57e3-4b95-b13e-2f7da451409d
-- title:
--   A CW cell piece contains the exact-profile power of its square block
-- statement:
--   Let $\rho = (\rho_X,\rho_Y,\rho_Z)$ be a coarse block type of the canonical square $CW_5 \otimes CW_5$. Let $N \ge 0$, let $\beta$ be complete-split profiles of level 2 in the three modes, and let $\mu_i(\sigma) = N\,\beta_i(\sigma)$ be the corresponding exact integer counts.
--
--   Consider the **cell piece**: the all-mode projection of $CW_5^{\otimes 2N}$, read as $N$ squares, onto the words in which every square has coarse grade $\rho_i$ in mode $i$ and whose fine-grade words occur exactly $\mu_i(\sigma)$ times.
--
--   **Statement.** This piece contains the exact-profile power of the canonical square block $\rho$ as a restriction:
--   $$\mathrm{restrictedPower}\big(T_\rho,\ \beta,\ \varepsilon = 0,\ N\big)\ \trianglelefteq\ \mathrm{unbroken}\big(N;\ \rho;\ \mu\big).$$
--
--   This connects the cell pieces produced by the More-Asymmetry regional extraction to the three-mode child values, which are stated for exact-profile powers of square blocks.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_tensor_rank

open MME

universe u

set_option autoImplicit false

theorem mme_canonical_square_piece_restricts_restrictedPower {K : Type u} [Field K]
    (ρ : Fin 3 → Fin 5) (N : ℕ) (beta : Fin 3 → CompleteSplit.Profile 2)
    (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i σ, (mu i σ : ℝ) = N * (beta i).probability σ) :
    TensorObj.Restrict
      (CompleteSplit.restrictedPower (CompleteSplitCanonicalSquare.obj K 5 ρ)
        (CompleteSplitCanonicalSquare.basis K 5 ρ) (CompleteSplitCanonicalSquare.label 5 ρ) beta 0 N)
      (RecursiveYZ.CWCells.unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ i ↦ (ρ i).val) (fun i _ ↦ mu i)) := by
  sorry
