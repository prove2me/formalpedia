-- Prove2me | Theorems.Thm_BookSixth_pointwise_isotopy_wrappers
-- name    : BookSixth.pointwise_isotopy_wrappers
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T09:06:49.686869+00:00
-- url     : https://prove2.me/theorems/33c10d39-2e98-4515-8d9e-44a91198f0a7
-- title:
--   Chapter 15: pointwise-time-map isotopy wrappers and the frame angle lemma
-- statement:
--   The three generic pieces of machinery needed to assemble the standardising isotopy of a round circle, stated so that they can be imported rather than rebuilt inside every proof. First, an isotopy wrapper: given pointwise mutually inverse time maps `A` and `B` that are jointly continuous in the time variable and satisfy `A 0 = id`, one obtains a continuous ambient isotopy of Euclidean three-space whose time map is `A t` at every time, not merely at time one. Second, the matching composition wrapper: the composite of two such pointwise isotopies is again a pointwise isotopy, with time map `G t (F t x)`. Third, an angle lemma: for any real pair `(a, b)` there is a real angle `θ` with `sin θ * a + cos θ * b = 0` and `cos θ * a - sin θ * b ≥ 0`. This is the angle that rotates a frame vector of a round circle onto a coordinate direction, and it is the ingredient that turns the two orthonormal directions of the circle into standard directions. These are needed to obtain the roundness-at-every-time form of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130.
-- source:
--   Restatement with pointwise time maps of the generic isotopy wrapper, the composition wrapper and the angle lemma used in the accepted proof of `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c), whose helpers are private to that proof file and therefore not importable. The wrapper is unchanged in substance: the homeomorphism is still constructed directly as `{ toFun := A t, invFun := B t, left_inv := hBA t, right_inv := hAB t }`, and the strengthened component `∀ t x, H t x = A t x` is a `rfl` because `toFun` is literally `A t`; the composition wrapper uses `Homeomorph.trans`. The angle lemma takes `θ = -Complex.arg (a + b i)`; the first identity follows from `Complex.sin_arg` and `Complex.cos_arg` by `ring`, and the second from the nonnegativity of `(a*a + b*b) / ‖(a + b i)‖`, with the zero pair handled separately. Needed as an importable dependency of `BookSixth.standardizing_time_maps_are_similarities` (theorem id 70d16099-287a-4360-bf09-e01ddf38bc25), whose hypothesis is needed by the accepted `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246) for Chapter 15, Theorem 1.

import Mathlib
import Definitions.Def_BookSixth

theorem BookSixth.pointwise_isotopy_wrappers :
    (∀ (A B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (hA : Continuous (fun p : ℝ × (Fin 3 → ℝ) => A p.1 p.2))
      (hB : Continuous (fun p : ℝ × (Fin 3 → ℝ) => B p.1 p.2))
      (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
      (h0 : ∀ x, A 0 x = x),
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = A t x)) ∧
    (∀ (F G : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (hF : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = F t x))
      (hG : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t x)),
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t (F t x))) ∧
    (∀ a b : ℝ, ∃ θ : ℝ, Real.sin θ * a + Real.cos θ * b = 0 ∧
        0 ≤ Real.cos θ * a - Real.sin θ * b) := by sorry
