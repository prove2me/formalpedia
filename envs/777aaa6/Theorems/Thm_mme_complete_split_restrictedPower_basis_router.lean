-- Prove2me | Theorems.Thm_mme_complete_split_restrictedPower_basis_router
-- name    : mme_complete_split_restrictedPower_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:13:52.94091+00:00
-- url     : https://prove2.me/theorems/8d8a5338-2b4e-43f3-8028-db9b888d2087
-- title:
--   Basis-labelled tensor maps preserve all complete-profile restrictions
-- statement:
--   Let $T$ and $S$ be three-tensors over any field, with chosen mode bases and a modewise linear map sending $T$ to $S$. Suppose every source basis vector maps to one target basis vector, and the associated complete fine-word labels agree. Then for every common triple of complete profiles $\beta$, every nonnegative tolerance $\varepsilon$, and every finite power $N$, the target's filtered power is a restriction of the source's filtered power:
--
--   $$S^{\otimes N}[\beta_X,\beta_Y,\beta_Z,\varepsilon]\;\leq_{\rm restr}\;T^{\otimes N}[\beta_X,\beta_Y,\beta_Z,\varepsilon].$$
--
--   This transfers actual all-three-mode profile projections along a label-preserving tensor router; it does not assume an extraction or a tensor-value bound. The complete labels, rather than single-coordinate marginals, must agree. Power zero uses the existing empty-word convention.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15). Elementary finite functoriality of that simultaneous profile projection, proved using the actual modewise tensor-power maps, their recursive basis action, and all-mode map descent. It is not a statement of the paper's asymptotic recursive extraction theorem.

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_kronPowModeMap_recursive_basis
import Theorems.Thm_mme_kronPow_modewise_maps_preserve_tensor

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped Classical NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_restrictedPower_basis_router
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I J : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (c : (i : Fin 3) → Basis (J i) K (S.V i))
    (f : (i : Fin 3) → T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (idx : (i : Fin 3) → I i → J i)
    (hbasis : ∀ i a, f i (b i a) = c i (idx i a))
    {ell : ℕ}
    (labelT : (i : Fin 3) → I i → CompleteWord ell)
    (labelS : (i : Fin 3) → J i → CompleteWord ell)
    (hlabel : ∀ i a, labelS i (idx i a) = labelT i a)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedPower S c labelS beta epsilon N)
      (restrictedPower T b labelT beta epsilon N) := by sorry
