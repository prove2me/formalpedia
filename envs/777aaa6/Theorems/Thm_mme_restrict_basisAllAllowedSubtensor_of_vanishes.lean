-- Prove2me | Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
-- name    : mme_restrict_basisAllAllowedSubtensor_of_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:41:56.875969+00:00
-- url     : https://prove2.me/theorems/95a0cd37-7a0c-477d-a091-56254bf46695
-- title:
--   An extraction descends through simultaneous three-mode basis filtering
-- statement:
--   Let T and A be three-tensors over any field. Choose a basis bᵢ in each mode of T and a predicate specifying its allowed basis vectors. Suppose modewise linear maps fᵢ carry T to A and satisfy
--   $$f_i(b_i(j))=0\quad\text{whenever }j\text{ is disallowed, for every mode }i.$$
--   Let T_allowed be the simultaneous three-mode projection retaining exactly the allowed basis spans. Then
--   $$A\preceq T_{\mathrm{allowed}}.$$
--   Thus a known extraction from the full source also extracts from the smaller, profile-filtered source when all three vanishing conditions are proved. An arbitrary extraction from T alone does not supply those conditions.
-- source:
--   All-three-mode generalization of the existing Prove2Me one-mode extraction-map descent lemma mme_restrict_basisZAllowedSubtensor_of_vanishes (a7d1ab3e-4ef4-48be-8fba-23977e9dd675). This is elementary linear algebra supplying the actual complete-profile landing required by More Asymmetry, arXiv:2404.16349v2, Definitions 3.4–3.6, printed pp.14–15, and the level-two extraction consumer of Proposition 6.3/Theorem 6.4. https://arxiv.org/abs/2404.16349v2. It does not establish a particular extraction's vanishing hypotheses or any asymptotic rate.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_tensor_rank

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_restrict_basisAllAllowedSubtensor_of_vanishes
    {K : Type u} [Field K] (T A : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop)
    (f : (i : Fin 3) → T.V i →ₗ[K] A.V i)
    (hmap : PiTensorProduct.map f T.t = A.t)
    (hvanish : ∀ i j, ¬ allowed i j → f i (b i j) = 0) :
    TensorObj.Restrict A (T.basisAllAllowedSubtensor b allowed) := by sorry
