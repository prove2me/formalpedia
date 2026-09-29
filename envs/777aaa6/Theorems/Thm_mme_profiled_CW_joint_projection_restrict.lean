-- Prove2me | Theorems.Thm_mme_profiled_CW_joint_projection_restrict
-- name    : mme_profiled_CW_joint_projection_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:50:17.812861+00:00
-- url     : https://prove2.me/theorems/9326c45c-fffb-4d9e-8f58-116d43bb508d
-- title:
--   Joint projection is a restriction of the product of part projections
-- statement:
--   Let $N$ positions be partitioned into parts $j$ of sizes $s_j$ by a bijection $\pi : \Sigma_j [s_j] \to [N]$. For each part $j$ let $T_j$ be a mode-wise predicate on fine words of length $s_j$. Let $Q$ be a mode-wise predicate on fine words of length $N$ such that every word allowed by $Q$ restricts, on every part $j$, to a word allowed by $T_j$.
--
--   Then the all-mode projection of $CW_5^{\otimes N}$ onto $Q$ is a restriction of the Kronecker product over the parts of the projections of $CW_5^{\otimes s_j}$ onto $T_j$:
--
--   $$\mathrm{proj}_Q\bigl(CW_5^{\otimes N}\bigr) \;\le\; \bigotimes_j \mathrm{proj}_{T_j}\bigl(CW_5^{\otimes s_j}\bigr).$$
--
--   This is the converse of the region product restriction, in which the product of the part projections restricts to the projection onto any predicate containing their conjunction. Together the two let a construction split positions into regions, work on each region separately, and then continue with a single predicate on all positions, as in More Asymmetry, Section 6.6 and Algorithm 1.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
open MME MME.TensorObj MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_profiled_CW_joint_projection_restrict {K : Type u} [Field K] {N parts : ℕ}
    (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (T : ∀ j, Predicate (size j)) (Q : Predicate N)
    (hQ : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩))) :
    TensorObj.Restrict (tensor K Q) (kronFin parts (fun j ↦ tensor K (T j))) := by sorry
