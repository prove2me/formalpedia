-- Prove2me | solution 1 for QuantizedWeightLattices.Landscape.lattice_infimum_close
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:31:35.104553+00:00
-- url     : https://prove2.me/submissions/b3c3f573-dd14-4d9b-abea-d1452a062165

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.Landscape Set Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [Nonempty E] {L : NNReal}
    {f : E → ℝ}
    (hL : LipschitzWith L f) (Q : Quantizer E) (hbdd : BddBelow (Set.range f)) :
    sInf (Set.range f) ≤ sInf (f '' Set.range Q.toFun) ∧
      sInf (f '' Set.range Q.toFun) ≤ sInf (Set.range f) + (L : ℝ) * Q.radius := by
  -- quantization moves `f` by at most `L · radius`
  have hlip : ∀ x, |f (Q.toFun x) - f x| ≤ (L : ℝ) * Q.radius := by
    intro x
    have h1 := hL.dist_le_mul (Q.toFun x) x
    rw [Real.dist_eq, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg)
  have hsub : f '' Set.range Q.toFun ⊆ Set.range f := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  have hne : (f '' Set.range Q.toFun).Nonempty :=
    ⟨_, ⟨Q.toFun (Classical.arbitrary E), ⟨_, rfl⟩, rfl⟩⟩
  have hbdd' : BddBelow (f '' Set.range Q.toFun) := hbdd.mono hsub
  refine ⟨csInf_le_csInf hbdd hne hsub, ?_⟩
  -- every value `f x` is within `L · radius` above some lattice value
  have hall : ∀ x, sInf (f '' Set.range Q.toFun) - (L : ℝ) * Q.radius ≤ f x := by
    intro x
    have h1 : sInf (f '' Set.range Q.toFun) ≤ f (Q.toFun x) :=
      csInf_le hbdd' ⟨Q.toFun x, ⟨x, rfl⟩, rfl⟩
    have h2 := (abs_le.1 (hlip x)).2
    linarith
  have := le_csInf (Set.range_nonempty f) (by
    rintro _ ⟨x, rfl⟩
    exact hall x)
  linarith
