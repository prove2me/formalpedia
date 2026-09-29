-- Prove2me | Theorems.Thm_mme_complete_split_CW_square_cyclic_profile_transport
-- name    : mme_complete_split_CW_square_cyclic_profile_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:24:59.320157+00:00
-- url     : https://prove2.me/theorems/a1be5b7c-df43-449a-9ad0-2887a9c250f1
-- title:
--   Cyclic transport of the actual canonical CW-square complete-profile restriction
-- statement:
--   Let $T_\rho$ be the actual canonical $q$-parameter Coppersmith–Winograd square constituent at coarse address $\rho$, with its fixed coordinate-pair basis and ordered two-grade labels. Write $F_{\beta,\varepsilon}$ for simultaneous complete-profile restriction in all three modes. For either nonidentity cyclic mode permutation $e$, every field, natural $q,N$, complete profiles $\beta$, and nonnegative tolerance $\varepsilon$,
--   \[
--   F_{\beta\circ e^{-1},\varepsilon}\bigl(T_{\rho\circ e^{-1}}^{\otimes N}\bigr)
--   \cong e\cdot F_{\beta,\varepsilon}\bigl(T_\rho^{\otimes N}\bigr).
--   \]
--   Here $\cong$ is actual mutual tensor restriction. New mode $i$ inherits old mode $e^{-1}(i)$; the same coordinate pair, its entire ordered two-grade label, and all $N$ power positions are preserved. At address $112$, one cyclic turn yields $211$ with profiles $(\beta_2,\beta_0,\beta_1)$ and two yield $121$ with $(\beta_1,\beta_2,\beta_0)$. This includes $q=0$ and $N=0$ and assumes no source isomorphism, extraction, or tensor-value estimate.
-- source:
--   Finite source adapter for the ordered complete profiles of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6, pp. 14–15, https://arxiv.org/abs/2404.16349v2. Combines the actual canonical CW-square cyclic tensor/basis transport with the proved generic complete-profile permutation naturality (b339c98c-0465-4db6-a41e-e01af025b748) and same-mode full-profile router (8d8a5338-2b4e-43f3-8028-db9b888d2087). This is a new finite formal adapter, not the paper's global extraction or numerical bound.

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_permutation

open MME MME.CompleteSplit
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_CW_square_cyclic_profile_transport
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (beta : Fin 3 → Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic
      (CompleteSplitCanonicalSquare.restrictedPower K q
        (fun i ↦ rho (e.symm i)) (fun i ↦ beta (e.symm i)) epsilon N)
      (TensorObj.permObj e
        (CompleteSplitCanonicalSquare.restrictedPower K q rho beta epsilon N)) := by sorry
