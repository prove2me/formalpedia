-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base
-- name    : mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T07:18:34.43183+00:00
-- url     : https://prove2.me/theorems/40ce2d8f-42b8-4cfc-b9e2-5e9121891830
-- title:
--   Exact-profile Table-2 collision degree can be fixed before prime selection
-- statement:
--   Fix a positive Table-2 scale m and let L be the corresponding source length. Reindex the complete marginal family to length L−1+1, and let T be its exact fifteen-component joint-profile subfamily. Then there are a finite ambient family A and a positive common collision degree d such that T has the prescribed multinomial cardinality, every X-marginal and Y-marginal fiber in A has cardinality d, and
--
--   $$
--   d \leq \bigl(6(L+1)\bigr)^5(L+1)^{15}\exp\!\left(mL_0\log 2\,\bigl(H_{\max}-H(\alpha_X)\bigr)\right),
--   $$
--
--   where L₀ is the fixed Table-2 scale constant. The construction of A and d is independent of the hashing prime. This is the non-circular base needed to choose a common prime only after the collision degree is known.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.1 (first hashing and exact-profile counting).

import Theorems.Thm_mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base
    (m : ℕ) (hm : 0 < m) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t // a t = s} =
        MME.DWZTable2Counts.component s * m
    ∃ d : ℕ, ∃ A : Finset (Fin (N + 1) → Fin 15),
      (∀ a, a ∈ A ↔ ∃ w ∈ A0,
        (fun t ↦ w (reindex t)) = a) ∧
      A.card = A0.card ∧
      (A.filter ExactProfile).card =
        Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) ∧
      0 < d ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeX (b t)) =
            (fun t ↦ MME.DWZSquare.shapeX (a t)))).card = d) ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeY (b t)) =
            (fun t ↦ MME.DWZSquare.shapeY (a t)))).card = d) ∧
      (d : ℝ) ≤
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
          (((L + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) := by
  sorry
