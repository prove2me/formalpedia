-- Prove2me | Theorems.Thm_mme_block_tensor_is_matMul_refined
-- name    : mme_block_tensor_is_matMul_refined
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-06-01T00:30:17.082621+00:00
-- url     : https://prove2.me/theorems/09c25380-f76c-4904-907e-03e9e561455b
-- statement:
--   **A single-triple block subtensor is Restrict-equivalent to a matrix-multiplication tensor of grading-class dimensions** — REFINED concrete version of `mme_block_tensor_is_matMul`. For every multi-type σ : Fin 3 → Fin t whose type-triple is in S (laser-aligned), the block subtensor `G.blockSubtensor σ` is Restrict-equivalent to MMObj K a b c where (a, b, c) = (finrank G.classOf 0 (σ 0), finrank G.classOf 1 (σ 1), finrank G.classOf 2 (σ 2)). Single-triple case is the building block; tensor-power blocks compose via `mme_graded_tensor_pow_block_decomp` (already PROVED). Proof: pick bases of grading classes, exhibit explicit Restrict witness mapping MM basis vectors to grading-class basis.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_block_tensor_is_matMul_refined {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t)) (_hsupport : TensorObj.LaserAlignedSupport G S) (σ : Fin 3 → Fin t) (_hσ : (σ 0, σ 1, σ 2) ∈ S) : TensorObj.Restrict (MMObj K (Module.finrank K (G.classOf 0 (σ 0) : Submodule K (T.V 0))) (Module.finrank K (G.classOf 1 (σ 1) : Submodule K (T.V 1))) (Module.finrank K (G.classOf 2 (σ 2) : Submodule K (T.V 2)))) (G.blockSubtensor σ) := by sorry
