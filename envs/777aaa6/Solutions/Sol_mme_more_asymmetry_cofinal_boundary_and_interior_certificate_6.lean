-- Prove2me | solution 6 for mme_more_asymmetry_cofinal_boundary_and_interior_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:41:31.515777+00:00
-- url     : https://prove2.me/submissions/bbbc3344-86a1-42b3-ba3f-8c41b434e53d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_explicit_child_witness

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ M : ∀ j, (A n j).ChildPlan K,
            (∏ j, (M j).dimA) = (D n).a ∧
            (∏ j, (M j).dimB) = (D n).b ∧
            (∏ j, (M j).dimC) = (D n).c ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤ ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by
  rcases mme_more_asymmetry_cofinal_explicit_child_witness (K := K) with
    ⟨D, A, V, error, hV, hpower, herror, hevent⟩
  refine ⟨D, A, V, error, hV, hpower, herror, ?_⟩
  filter_upwards [hevent] with n hn
  rcases hn with
    ⟨hraw, a, b, c, ha, hb, hc, hcases, hlower, hcopies, hbudget, hrate⟩
  let M : ∀ j, (A n j).ChildPlan K := fun j ↦
    { a := a j
      b := b j
      c := c j
      cases := hcases j }
  refine ⟨hraw, M, ?_, ?_, ?_, hlower, hcopies, hbudget, hrate⟩
  · simpa [M, Stage.ChildPlan.dimA] using ha
  · simpa [M, Stage.ChildPlan.dimB] using hb
  · simpa [M, Stage.ChildPlan.dimC] using hc
