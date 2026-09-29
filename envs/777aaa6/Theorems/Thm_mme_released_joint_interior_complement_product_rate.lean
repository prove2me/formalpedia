-- Prove2me | Theorems.Thm_mme_released_joint_interior_complement_product_rate
-- name    : mme_released_joint_interior_complement_product_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:36:15.407392+00:00
-- url     : https://prove2.me/theorems/c81b3ce9-1178-46d9-9029-ab97e0a13699
-- title:
--   The complete complementary product retains all boundary rates
-- statement:
--   All 270 complementary factors admit one positive matrix family at the sum of their complete rates. Boundary profiles and scalar rate certificates are fixed before the common replication scale, tolerance, field, and exponent are chosen. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_complement_cell_rate
import Theorems.Thm_mme_six_product_exponential_extraction
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.ReleasedJointInterior
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.CompleteSplit Filter
universe u

theorem mme_released_joint_interior_complement_product_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    let c : Fin 270 → Shape := fun j => shapeEquiv (component j).2
    ∃ rate : Fin 270 → ℝ,
      (∀ j, (0 < weight j ∨ coarseCounts (component j).1 (c j) = 0) → rate j = 0) ∧
      (∀ j, ¬ 0 < weight j → 0 < coarseCounts (component j).1 (c j) →
        ∃ (z : Fin 3) (B : Boundary.Profile 3 (coarseCounts (component j).1 (c j))),
          ((c j).val z).val = 0 ∧
          (∀ i w, wordCounts (component j).1 i (c j) w = B.mu z i w) ∧
          rate j = (coarseCounts (component j).1 (c j) : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => (B.count w : ℝ) /
              (coarseCounts (component j).1 (c j) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (eps : ℝ), 0 ≤ eps →
        ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
          let L : Fin 270 → ℕ := fun j => k * coarseCounts (component j).1 (c j)
          let T : Fin 270 → TensorObj K 3 := fun j => permObj (roleEquiv (component j).1)
            ((source K 5 3 (L j)).basisAllAllowedSubtensor (basis K 5 3 (L j)) (fun i x =>
              (∀ r, grade (label 5 3 (L j) (Equiv.refl _) x r) = ((c j).val i).val) ∧
              if L j = 0 then ∀ w, |(profile (component j).1).2 i ⟨0,c j⟩ w| ≤ eps
              else ∀ w,
                |(count (fun _ : Fin (L j) => Unit.unit)
                  (label 5 3 (L j) (Equiv.refl _) x) Unit.unit w : ℝ) / (L j : ℝ) -
                  ((blocks k : ℝ) / (L j : ℝ)) * (profile (component j).1).2 i ⟨0,c j⟩ w| ≤
                  ((blocks k : ℝ) / (L j : ℝ)) * eps))
          ∃ (q : ℕ) (a b d : Fin q → ℕ), 0 < q ∧
            Restrict (bigAdd (fun i => MMObj K (a i) (b i) (d i)))
              (sixSymmetrization (kronFin 270
                (fun j => if 0 < weight j then oneObj else T j))) ∧
            Real.exp (∑ j, 6 * tau * ((k : ℝ) * rate j)) ≤
              ∑ i, (((a i * b i * d i : ℕ) : ℝ) ^ tau) := by sorry
