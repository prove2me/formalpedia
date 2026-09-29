-- Prove2me | Theorems.Thm_mme_complete_split_restrictedPower_perm_naturality
-- name    : mme_complete_split_restrictedPower_perm_naturality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T03:39:47.088861+00:00
-- url     : https://prove2.me/theorems/b339c98c-0465-4db6-a41e-e01af025b748
-- title:
--   Complete-word profile restriction commutes with arbitrary tensor-mode permutation
-- statement:
--   Let $T$ be an order-three tensor over any field, with chosen mode bases, complete fine-word labels, and a triple of complete profiles $\beta$. Write $F_{\beta,\varepsilon}(T^{\otimes N})$ for its simultaneous complete-profile restriction. For every mode permutation $e$, nonnegative tolerance $\varepsilon$, and natural power $N$,
--   \[
--   F_{\beta\circ e^{-1},\varepsilon}\bigl((e\cdot T)^{\otimes N}\bigr)
--   \cong e\cdot F_{\beta,\varepsilon}(T^{\otimes N}).
--   \]
--   On the left, the basis and full label map in new mode $i$ are also taken from old mode $e^{-1}(i)$. The isomorphism is actual mutual tensor restriction. The entire basis-word index, all $N$ power positions, and every ordered fine letter are preserved; only the tensor modes are relabeled. This includes $N=0$ under the explicit empty-word convention. No source isomorphism, extraction, or value bound is assumed.
-- source:
--   Finite naturality of the simultaneous ordered complete-profile projection in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6, pp. 14–15, https://arxiv.org/abs/2404.16349v2. Exact tensor-power/mode-permutation linear equivalences and their recursive basis action are already proved publicly (78840018-6aa1-4729-9d11-af4bc22a9493 and f3523656-332d-4129-a59e-fd5c5248d54a). The theorem combines them with all-mode projection descent and the existing permuted block-subtensor identity. It is a new finite formal adapter, not a separately numbered source theorem or the paper's global extraction result.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_permutation

open MME MME.CompleteSplit Module
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_restrictedPower_perm_naturality
    {K : Type u} [Field K] (T : TensorObj K 3)
    (e : Equiv.Perm (Fin 3)) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic
      (restrictedPower (TensorObj.permObj e T)
        (fun i ↦ b (e.symm i)) (fun i ↦ label (e.symm i))
        (fun i ↦ beta (e.symm i)) epsilon N)
      (TensorObj.permObj e (restrictedPower T b label beta epsilon N)) := by sorry
