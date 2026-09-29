-- Prove2me | solution 1 for VectorSpaceOpt.orthogonal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:26.939294+00:00
-- url     : https://prove2.me/submissions/0a44a159-35e9-4a15-b4f7-4b0a06b86f70

import Mathlib
open scoped RealInnerProductSpace

section VSMAux
variable {Hh : Type*} [NormedAddCommGroup Hh] [InnerProductSpace ℝ Hh]

theorem vsm_best_iff_iInf (K : Set Hh) (x : Hh) {v : Hh} (hv : v ∈ K) :
    (∀ w ∈ K, ‖x - v‖ ≤ ‖x - w‖) ↔ ‖x - v‖ = ⨅ w : K, ‖x - w‖ := by
  haveI : Nonempty K := ⟨⟨v, hv⟩⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖x - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨fun h => le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨v, hv⟩),
    fun h w hw => h ▸ ciInf_le hbdd ⟨w, hw⟩⟩

theorem vsm_best_of_orth (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M)
    (h : ∀ m ∈ M, ⟪x - v, m⟫ = 0) : ∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖ := by
  intro m hm
  have hsq : ‖x - m‖ ^ 2 = ‖x - v‖ ^ 2 + ‖v - m‖ ^ 2 := by
    have hsplit : x - m = (x - v) + (v - m) := by abel
    rw [hsplit, norm_add_sq_real, h _ (M.sub_mem hv hm)]; ring
  nlinarith [norm_nonneg (x - v), norm_nonneg (x - m), sq_nonneg ‖v - m‖]

theorem vsm_orth_iff_best (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M) :
    (∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖) ↔ (∀ m ∈ M, ⟪x - v, m⟫ = 0) :=
  ⟨fun h => (Submodule.norm_eq_iInf_iff_real_inner_eq_zero M hv).1
      ((vsm_best_iff_iInf (M : Set Hh) x hv).1 h),
   vsm_best_of_orth M x v hv⟩

end VSMAux


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) :
    (∀ x : H, ∃! p : H × H, p.1 ∈ M ∧ p.2 ∈ Mᗮ ∧ x = p.1 + p.2) ∧ Mᗮᗮ = M := by
  haveI : CompleteSpace M := hM.completeSpace_coe
  have hic : IsCompl M Mᗮ := M.isCompl_orthogonal_of_hasOrthogonalProjection
  refine ⟨fun x => ?_, M.orthogonal_orthogonal⟩
  obtain ⟨u, v, huv, -⟩ := Submodule.existsUnique_add_of_isCompl hic x
  refine ⟨((u : H), (v : H)), ⟨u.2, v.2, huv.symm⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hx⟩
  have hab : a + b = (u : H) + v := by rw [← hx, huv]
  have h1 : a - (u : H) = (v : H) - b := by
    have : a - (u : H) - ((v : H) - b) = (a + b) - ((u : H) + v) := by abel
    rw [hab, sub_self] at this
    exact sub_eq_zero.1 this
  have hmM : a - (u : H) ∈ M := M.sub_mem ha u.2
  have hmO : a - (u : H) ∈ Mᗮ := h1 ▸ Mᗮ.sub_mem v.2 hb
  have hz : a - (u : H) = 0 := (Submodule.disjoint_def.1 hic.disjoint) _ hmM hmO
  have hau : a = (u : H) := sub_eq_zero.1 hz
  have hbv : b = (v : H) := by
    rw [hau] at hab
    exact add_left_cancel hab
  exact Prod.ext hau hbv
