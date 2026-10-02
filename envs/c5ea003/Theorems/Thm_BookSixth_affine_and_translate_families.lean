-- Prove2me | Theorems.Thm_BookSixth_affine_and_translate_families
-- name    : BookSixth.affine_and_translate_families
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T09:01:09.385153+00:00
-- url     : https://prove2.me/theorems/b8bae589-c31e-4c3c-9a2b-63c52a2e8ed3
-- title:
--   Chapter 15: the affine rescaling and translation isotopy families, pointwise in time
-- statement:
--   Two of the component families of the standardising isotopy of a single round circle, stated so that they can be imported rather than rebuilt. The first is the affine rescaling about a centre `c` by the factor `exp (-(t * log r))`, which is strictly positive for every real `t` whenever `r > 0`; it is the step that removes the radius of the round circle. The second is the translation by `t • a`, which places the circle at its final location. Each is a continuous ambient isotopy of Euclidean three-space that starts at the identity and whose time map is given explicitly at every time, not only at time one. These are the two non-rotational families of the accepted `BookSixth.round_circle_single_standardize`, restated with pointwise time maps, and they are needed to obtain the roundness-at-every-time form of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130.
-- source:
--   Restatement with pointwise time maps of the affine rescaling family and the translation family used in the accepted proof of `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c), whose helpers are private to that proof file and therefore not importable. Both are built directly as `Homeomorph`s with `toFun` the forward time map and `invFun` the backward one, so no choice-generated inverse is used; the two inverse identities are discharged by `Real.exp_add`, `Real.exp_zero` and elementary `add_sub`/`sub_add` cancellation. The only change from the accepted helpers is that the final component holds at every `t` rather than only at `t = 1`. Needed as an importable dependency of `BookSixth.standardizing_time_maps_are_similarities` (theorem id 70d16099-287a-4360-bf09-e01ddf38bc25), whose hypothesis is needed by the accepted `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246) for Chapter 15, Theorem 1.

import Mathlib
import Definitions.Def_BookSixth

theorem BookSixth.affine_and_translate_families :
    (∀ (c : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r),
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧
        (∀ t x, H t x = Real.exp (-(t * Real.log r)) • (x - t • c))) ∧
    (∀ a : Fin 3 → ℝ,
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = x + t • a)) := by sorry
