-- Prove2me | Theorems.Thm_mme_profiled_CW_region_product_restrict
-- name    : mme_profiled_CW_region_product_restrict
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:12:55.653484+00:00
-- url     : https://prove2.me/theorems/6ddbbcea-478d-45c1-bee5-efe958bd471b
-- title:
--   Disjoint position regions of a profiled CW power
-- statement:
--   Partition the $N$ elementary CW5 positions into finitely many regions of sizes $n_j$. Give region $j$ a profile predicate $Q_j$, and suppose satisfying all regional predicates implies the parent predicate $P$. Then
--
--   $$\bigotimes_j \operatorname{CW}_5^{n_j}[Q_j]\ \le\ \operatorname{CW}_5^N[P].$$
--
--   The restriction uses the actual position bijection and projections; it retains the parent constraints.
-- source:
--   Constructive tensor-algebra components for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorem 6.4. These lemmas implement the finite operations; they do not assert the numerical witness.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
open BigOperators MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_profiled_CW_region_product_restrict {K : Type u} [Field K] {N parts : ℕ} (P : Predicate N)
    (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (Q : ∀ j, Predicate (size j))
    (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x) :
    Restrict (kronFin parts (fun j ↦ tensor K (Q j))) (tensor K P) := by sorry
