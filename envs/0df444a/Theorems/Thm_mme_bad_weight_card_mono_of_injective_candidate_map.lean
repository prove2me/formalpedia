-- Prove2me | Theorems.Thm_mme_bad_weight_card_mono_of_injective_candidate_map
-- name    : mme_bad_weight_card_mono_of_injective_candidate_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:02:10.265101+00:00
-- url     : https://prove2.me/theorems/87ecbf41-1848-400b-bfa2-2ec3a94768b9
-- title:
--   Bad collision weights are monotone under candidate embeddings
-- statement:
--   Let a finite candidate family embed injectively into a larger finite family, and suppose survival at every weight is preserved by the embedding. Then every weight at which at least two small candidates survive also has at least two large survivors. Consequently, the number of bad collision weights for the small family is at most the number for the large family. This transports Claim-6.8 collision estimates from a full fixed-address fiber to a selected subfamily.
-- source:
--   Elementary finite-cardinality monotonicity used in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem mme_bad_weight_card_mono_of_injective_candidate_map
    {Small Big Weight : Type*}
    [Fintype Small] [DecidableEq Small]
    [Fintype Big] [DecidableEq Big]
    [Fintype Weight] [DecidableEq Weight]
    (smallRel : Small → Weight → Prop) [DecidableRel smallRel]
    (bigRel : Big → Weight → Prop) [DecidableRel bigRel]
    (f : Small → Big) (hf : Function.Injective f)
    (hrel : ∀ a w, smallRel a w → bigRel (f a) w) :
    (Finset.univ.filter (fun w : Weight ↦
      1 < (Finset.univ.filter (fun a : Small ↦ smallRel a w)).card)).card ≤
    (Finset.univ.filter (fun w : Weight ↦
      1 < (Finset.univ.filter (fun b : Big ↦ bigRel b w)).card)).card := by
  sorry
