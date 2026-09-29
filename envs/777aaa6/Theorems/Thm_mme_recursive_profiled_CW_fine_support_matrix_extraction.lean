-- Prove2me | Theorems.Thm_mme_recursive_profiled_CW_fine_support_matrix_extraction
-- name    : mme_recursive_profiled_CW_fine_support_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:08:37.435119+00:00
-- url     : https://prove2.me/theorems/e55c60a4-a1d0-4a44-89da-5145b1170e27
-- title:
--   Explicit matrix extraction from a supported fine-grade assignment
-- statement:
--   Let $P_i$ be predicates on length-$N$ words over $\{0,1,2\}$, and let $T_P$ be the corresponding three-mode coordinate projection of $\mathrm{CW}_5^{\otimes N}$ over any field $K$. Suppose words $x_0,x_1,x_2$ satisfy $P_i(x_i)$ and
--
--   $$x_0(r)+x_1(r)+x_2(r)=2\qquad(0\leq r<N).$$
--
--   For $i\ne j$, put $n_{ij}=|\{r:x_i(r)=x_j(r)=1\}|$. Then
--
--   $$\langle 5^{n_{02}},5^{n_{01}},5^{n_{12}}\rangle_K\ \preceq\ T_P.$$
--
--   Thus any simultaneously supported fine-grade assignment provides an actual matrix restriction with explicit dimensions. This statement holds for arbitrary mode predicates and all finite lengths, including zero. It accounts for one fixed grade assignment, without claiming an additional multiplicity gain from other assignments.
-- source:
--   Singleton elementary boundary profiles and exact profiled CW boundary termination; flattening/splitting identifies the literal intact block.

import Theorems.Thm_mme_recursive_profiled_CW_boundary_end

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary MME.ProfiledCW

theorem mme_recursive_profiled_CW_fine_support_matrix_extraction {K : Type*} [Field K] {N : ℕ}
    (P : Predicate N) (x : Fin 3 → FineWord N)
    (hs : supported x) (hx : ∀ i, P i (x i)) :
    Restrict (MMObj K
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 2 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 1 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 1 r).val = 1 ∧ (x 2 r).val = 1)).card))
      (tensor K P) := by sorry
