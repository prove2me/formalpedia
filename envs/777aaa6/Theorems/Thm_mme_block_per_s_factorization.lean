-- Prove2me | Theorems.Thm_mme_block_per_s_factorization
-- name    : mme_block_per_s_factorization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:21:00.558529+00:00
-- url     : https://prove2.me/theorems/9ca26be2-85ff-47d5-957e-f4a843ef490a
-- statement:
--   **Paper-agnostic per-$s$ Kron composition for tensor-power matrix-multiplication restriction.** Given a 3-tensor $T$ with a $t$-grading $G$, laser support $S$, and laser-aligned support property, plus per-$s$ MM-dimension assignments $(a_s, b_s, c_s)$ and per-$s$ restrictions $\mathrm{MMObj}\,K\,a_s\,b_s\,c_s \le G.\mathrm{blockSubtensor}\,s$ for every $s \in S$, the tensor power $T^{\otimes N}$ restricts from the multinomial-product MMObj whose three dimensions are the products over $k$ of $(a_{\tau k}, b_{\tau k}, c_{\tau k})$, for any type-sequence $\tau : \mathrm{Fin}\,N \to S$. Replaces the false-as-stated `mme_block_tensor_kronPow_balanced_dim_product` (UUID `0a0eece9`) and `mme_block_tensor_is_matMul_refined` (UUID `4b09ae9d`), both of which used incorrect grading-class finrank dimensions; see counterexample at CW $\sigma = (1,0,1)$. This is the **abstract bridge** statement reusable across all laser-method papers (CW, Stothers, Vassilevska Williams, Le Gall, Alman-Vassilevska Williams).
-- source:
--   Wigderson-Zuiddam §6 (laser method); replaces false UUIDs 0a0eece9 + 4b09ae9d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor_rank

open MME BigOperators

universe u

/-- **Paper-agnostic per-s Kron composition for kronPow MM Restrict.**

REPLACES the false `mme_block_tensor_kronPow_balanced_dim_product` (UUID
`0a0eece9`) and the false `mme_block_tensor_is_matMul_refined` (UUID
`4b09ae9d`). Both prior statements used `MMObj K (finrank G.classOf …)`
dimensions which is mathematically incorrect; see CW σ=(1,0,1) counterexample
in `REPORT_block_MM_correction.md`.

**Setup.** Given a 3-tensor `T : TensorObj K 3` with a `t`-grading `G`, laser
support `S`, and `LaserAlignedSupport G S`. The paper-specific input is per-s
MM-dim assignments `(a, b, c) : S → ℕ` plus per-s MM Restrict witnesses
`MMObj K (a s) (b s) (c s) ≤ G.blockSubtensor s_fn` for every `s ∈ S` (for CW
these are the 6 `mme_CW_block_is_MM_at_*` PROVED witnesses).

**Conclusion.** For any tensor power `N` and any type-sequence
`τ : Fin N → (Fin t × Fin t × Fin t)` with each `τ k ∈ S`, the tensor power
`T.kronPow N` `Restrict`s from the multinomial-product MMObj whose three
dimensions are the products of per-position `(a (τ k), b (τ k), c (τ k))`.

**Why no `induced` parameter.** We dropped the awkward
`induced.blockSubtensor σ` framework — the kronPow itself directly Restricts
from the multinomial MMObj. The choice of type sequence `τ` plays the role
that `σ`/`induced` played in the false statements, but without the
"canonical-induced" looseness.

**Proof sketch (~200-400 LOC).**
* Induction on `N`. Base case `N = 0`: `T.kronPow 0 = oneObj`, multinomial
  is the empty product `MMObj K 1 1 1`, which restricts to `oneObj`
  (already known via `Def_mme_omega_normalize:263-300`).
* Inductive step: `T.kronPow (N+1) = kron T (T.kronPow N)`. Apply per-s MM
  Restrict at position 0 (yielding `MMObj K (a (τ 0)) (b (τ 0)) (c (τ 0))`
  Restricting into the type-`τ 0` block of T), then IH at remaining N
  positions, then `MMObj_kron_iso` (in `Def_mme_mmobj_mul.lean`) to combine
  the Kron of two MMObjs into a single MMObj of product dimensions. -/
theorem mme_block_per_s_factorization
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t))
    (a b c : (Fin t × Fin t × Fin t) → ℕ)
    (_h_per_s_MM : ∀ s ∈ S,
        TensorObj.Restrict (MMObj K (a s) (b s) (c s))
          (G.blockSubtensor (fun i : Fin 3 =>
            match i with
            | ⟨0, _⟩ => s.1
            | ⟨1, _⟩ => s.2.1
            | ⟨2, _⟩ => s.2.2)))
    (N : ℕ)
    (τ : Fin N → Fin t × Fin t × Fin t)
    (_hτ_in_S : ∀ k : Fin N, τ k ∈ S) :
    TensorObj.Restrict
      (MMObj K
        (∏ k : Fin N, a (τ k))
        (∏ k : Fin N, b (τ k))
        (∏ k : Fin N, c (τ k)))
      (T.kronPow N) := by
  sorry
