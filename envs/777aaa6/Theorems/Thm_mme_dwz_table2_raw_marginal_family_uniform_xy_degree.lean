-- Prove2me | Theorems.Thm_mme_dwz_table2_raw_marginal_family_uniform_xy_degree
-- name    : mme_dwz_table2_raw_marginal_family_uniform_xy_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:13:09.697118+00:00
-- url     : https://prove2.me/theorems/9a7e2749-b10a-490f-8810-42fcb1b2288d
-- title:
--   Uniform X/Y degree and explicit rate for the raw Table-2 marginal family
-- statement:
--   For the finite family of raw length-$L$ Table-2 component words with all three prescribed marginals, where $L$ is the integral Table-2 scale times $m$, there is one positive integer $d$ such that every X-star and every Y-star has exactly $d$ elements. The same $d$ satisfies the published explicit polynomial-times-exponential upper bound with exponent $\max H-H(\alpha_X)$. This transports the subtype-level uniform degree theorem into the raw finite-family representation used by affine hashing.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Equation (21), Section 3.10, and Table 2.

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree_rate

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_raw_marginal_family_uniform_xy_degree (m : ℕ) :
    let L := MME.DWZTable2Counts.scale * m
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
    let A : Finset (Fin L → Fin 15) := Finset.univ.filter P
    ∃ d : ℕ,
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
