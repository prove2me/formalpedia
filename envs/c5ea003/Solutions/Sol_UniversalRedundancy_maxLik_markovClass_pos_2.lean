-- Prove2me | solution 2 for UniversalRedundancy.maxLik_markovClass_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:11:27.259663+00:00
-- url     : https://prove2.me/submissions/412083c1-3312-4b1c-b8db-ac2537e7725f

import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Markov
import Definitions.Def_MachineLearning_UniversalRedundancy_Types

open UniversalRedundancy Finset

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem solution (n : ℕ) (x : Fin (n + 1) → A) :
    0 < (markovClass A n).maxLik x := by
  classical
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos
    positivity
  -- Reuse the same construction as Nonempty (MarkovParam A)
  let θ : MarkovParam A :=
    ⟨(fun _ => (Fintype.card A : ℝ)⁻¹, fun _ _ => (Fintype.card A : ℝ)⁻¹),
      ⟨⟨fun _ => by positivity, by
          rw [sum_const, card_univ, nsmul_eq_mul]; field_simp⟩,
        fun _ => ⟨fun _ => by positivity, by
          rw [sum_const, card_univ, nsmul_eq_mul]; field_simp⟩⟩⟩
  have hpos : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hprob : 0 < (markovClass A n).prob θ x := by
    change 0 < _ * _
    refine mul_pos (inv_pos.mpr hpos) (prod_pos fun _ _ => inv_pos.mpr hpos)
  have hbdd : BddAbove (Set.range fun θ' : MarkovParam A => (markovClass A n).prob θ' x) := by
    refine ⟨1, ?_⟩
    intro y hy
    obtain ⟨θ', rfl⟩ := hy
    have : (markovClass A n).prob θ' x ≤ ∑ z, (markovClass A n).prob θ' z :=
      single_le_sum (fun z _ => (markovClass A n).nonneg θ' z) (mem_univ x)
    simpa [(markovClass A n).sum_one θ'] using this
  have hle : (markovClass A n).prob θ x ≤ (markovClass A n).maxLik x := by
    simpa [SourceClass.maxLik] using le_ciSup hbdd θ
  linarith
