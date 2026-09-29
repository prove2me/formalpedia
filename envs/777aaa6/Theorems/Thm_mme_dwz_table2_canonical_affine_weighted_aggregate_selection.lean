-- Prove2me | Theorems.Thm_mme_dwz_table2_canonical_affine_weighted_aggregate_selection
-- name    : mme_dwz_table2_canonical_affine_weighted_aggregate_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:39:46.49035+00:00
-- url     : https://prove2.me/theorems/4f5e325d-b642-4a7b-a74e-e7da5777d0f7
-- title:
--   Canonical affine bucket selects an isolated aggregate-mass family
-- statement:
--   Let $T$ be a target family of Table-2 words inside an ambient family $A$, and let the canonical asymmetric affine hash use a three-term-progression-free label set $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$. Suppose each target word has at most $d$ ambient competitors sharing its $X$-word and at most $d$ sharing its $Y$-word, with $8d\le p$. Give each surviving target word a mass between $0$ and a common capacity $c$, and assume the total mass over all affine states is at least seven eighths of the full incidence capacity. Then one affine state $q$ contains a subfamily $I\subseteq T$ that is isolated against the entire bucket in both $X$ and $Y$, and satisfies
--
--   $$\frac{|T|\,|S|}{2p^2}\le\sum_{a\in I}\frac{\operatorname{mass}(q,a)}{c}.$$
--
--   This is the quantitative common-state selector required by the source-faithful aggregate version of the DWZ asymmetric hash. It is tensor-independent so that broken-copy nonhole mass and Step-1-filtered source maps can be supplied separately.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6, first-hash pruning and aggregate Claim 6.8 mass accounting (pp. 50--54); finite weighted double-counting formalization.

import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_incidence_factory
import Theorems.Thm_mme_dwz_asymmetric_hash_exact_incidence_sums
import Theorems.Thm_mme_dwz_target_two_mode_collision_card_le_of_degree
import Theorems.Thm_mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
import Theorems.Thm_mme_finset_weighted_collision_averaging_isolated

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_canonical_affine_weighted_aggregate_selection
    {p N : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d cap : ℕ) (hcap : 0 < cap) (hmod : 8 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeX (b t)) =
          (fun t ↦ DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeY (b t)) =
          (fun t ↦ DWZSquare.shapeY (a t)))).card ≤ d)
    (mass : ((Fin (N + 2) → ZMod p) × ZMod p) →
      (Fin (N + 1) → Fin 15) → ℕ)
    (hmassCap : ∀ q a, a ∈ T →
      a ∈ dwzTable2AffineHashBucket S A q → mass q a ≤ cap)
    (hmassTotal :
      (7 / 8 : ℝ) *
          ((cap : ℝ) * (T.card : ℝ) * (S.card : ℝ) *
            (p : ℝ) ^ (N + 1)) ≤
        ∑ q : (Fin (N + 2) → ZMod p) × ZMod p,
          (((∑ a ∈ T.filter (fun a ↦
            a ∈ dwzTable2AffineHashBucket S A q), mass q a) : ℕ) : ℝ)) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
      ∃ I : Finset (Fin (N + 1) → Fin 15),
        I ⊆ T ∧
        I ⊆ dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I, ∀ e' ∈ dwzTable2AffineHashBucket S A q,
          (fun t ↦ DWZSquare.shapeX (e t)) =
              (fun t ↦ DWZSquare.shapeX (e' t)) ∨
            (fun t ↦ DWZSquare.shapeY (e t)) =
              (fun t ↦ DWZSquare.shapeY (e' t)) → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by
  sorry
