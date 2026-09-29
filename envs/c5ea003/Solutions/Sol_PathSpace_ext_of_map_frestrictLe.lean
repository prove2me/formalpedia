-- Prove2me | solution 1 for PathSpace.ext_of_map_frestrictLe
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:53:36.435978+00:00
-- url     : https://prove2.me/submissions/10349747-a797-4e38-abf5-0a797cdc8428

import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- Two finite measures on the path space agreeing on all `Iic n` marginals are equal. -/
theorem solution {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    {μ ν : Measure (Π n, X n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  set fam : (n : ℕ) → Measure (Π i : Iic n, X i) := fun n => μ.map (frestrictLe n) with hfam
  have hproj : ∀ a b : ℕ, ∀ hab : a ≤ b, (fam b).map (frestrictLe₂ hab) = fam a := by
    intro a b hab
    simp only [hfam]
    rw [Measure.map_map (measurable_frestrictLe₂ hab) (measurable_frestrictLe b),
      frestrictLe₂_comp_frestrictLe hab]
  have hPF := isProjectiveMeasureFamily_inducedFamily fam hproj
  have hμ : IsProjectiveLimit μ (inducedFamily fam) := by
    rw [isProjectiveLimit_nat_iff hPF]
    intro n
    rw [inducedFamily_Iic]
  have hν : IsProjectiveLimit ν (inducedFamily fam) := by
    rw [isProjectiveLimit_nat_iff hPF]
    intro n
    rw [inducedFamily_Iic]
    exact (h n).symm
  exact hμ.unique hν
