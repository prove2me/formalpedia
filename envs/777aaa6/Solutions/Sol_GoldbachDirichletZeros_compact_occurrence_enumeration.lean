-- Prove2me | solution 1 for GoldbachDirichletZeros.compact_occurrence_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:16:33.946672+00:00
-- url     : https://prove2.me/submissions/be1e360a-903b-4af7-b073-f3c33d27044f

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

open Complex Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

namespace GoldbachZeroMultiset

private noncomputable def regularized {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : ℂ → ℂ := by
  classical
  exact if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ N
    else DirichletCharacter.LFunction χ

private lemma regularized_differentiable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Differentiable ℂ (regularized χ) := by
  classical
  by_cases hχ : χ = 1
  · simpa [regularized,hχ] using DirichletCharacter.differentiable_LFunctionTrivChar₁ N
  · simpa [regularized,hχ] using DirichletCharacter.differentiable_LFunction hχ

private lemma regularized_one_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : regularized χ 1 ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · simpa [regularized,hχ] using DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
  · simpa [regularized,hχ] using DirichletCharacter.LFunction_apply_one_ne_zero hχ

private lemma regularized_zero_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    regularized χ s = 0 ↔ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0 := by
  classical
  by_cases hs : s = 1
  · subst s
    simp [regularized_one_ne_zero χ]
  · by_cases hχ : χ = 1
    · simp [regularized,hχ,DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar,hs,
        mul_eq_zero,sub_ne_zero.mpr hs]
    · simp [regularized,hχ,hs]

private lemma original_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1) :
    AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1}) ?_ (isOpen_ne.mem_nhds hs)
  intro z hz
  exact (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt

private lemma regularized_order {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1) :
    analyticOrderAt (regularized χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s := by
  classical
  by_cases hχ : χ = 1
  · have he : regularized χ =ᶠ[𝓝 s]
        (fun z : ℂ => (z-1)*DirichletCharacter.LFunction χ z) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz
      simp [regularized,hχ,DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne hz,DirichletCharacter.LFunctionTrivChar]
    rw [analyticOrderAt_congr he]
    have ha : AnalyticAt ℂ (fun z : ℂ => z-1) s := by fun_prop
    have ho : analyticOrderAt (fun z : ℂ => z-1) s = 0 :=
      ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    change analyticOrderAt ((fun z : ℂ => z-1)*DirichletCharacter.LFunction χ) s = _
    rw [analyticOrderAt_mul ha (original_analytic χ s hs),ho,zero_add]
  · simp [regularized,hχ]

private lemma regularized_finite_order {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    analyticOrderAt (regularized χ) s ≠ ⊤ := by
  have hd := regularized_differentiable χ
  have ha : AnalyticOnNhd ℂ (regularized χ) univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hd
  have ho : analyticOrderAt (regularized χ) (1:ℂ) = 0 :=
    (hd.analyticAt 1).analyticOrderAt_eq_zero.mpr (regularized_one_ne_zero χ)
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1:ℂ)) (mem_univ s) (ho ▸ by simp)

private lemma compact_proper_zeros_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (K : Set ℂ) (hK : IsCompact K) :
    (K ∩ {s | s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}).Finite := by
  have hd := regularized_differentiable χ
  have ha : AnalyticOnNhd ℂ (regularized χ) univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hd
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (regularized_one_ne_zero χ) (mem_univ (1:ℂ)) isConnected_univ
  have hz : IsDiscrete {s | regularized χ s = 0} := by
    simpa using isDiscrete_of_codiscreteWithin hc
  have hclosed : IsClosed {s | regularized χ s = 0} :=
    isClosed_eq hd.continuous continuous_const
  have hf := (hK.inter_right hclosed).finite (hz.mono inter_subset_right)
  simpa only [regularized_zero_iff] using hf

private lemma proper_zero_multiplicity {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    ((analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat : ENat) =
      analyticOrderAt (DirichletCharacter.LFunction χ) s ∧
    0 < (analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat := by
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
    rw [← regularized_order χ s hs]
    exact regularized_finite_order χ s
  have hcast := ENat.coe_toNat hfinite
  refine ⟨hcast,?_⟩
  have hnonzero := (original_analytic χ s hs).analyticOrderAt_ne_zero.mpr hz
  by_contra h
  have hnat : (analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat = 0 := by omega
  rw [hnat] at hcast
  exact hnonzero hcast.symm

end GoldbachZeroMultiset

theorem solution (N : ℕ) [NeZero N] (K : Set ℂ) (hK : IsCompact K) :
    (∀ χ : DirichletCharacter ℂ N,
      (K ∩ {s | s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}).Finite) ∧
    (∀ (χ : DirichletCharacter ℂ N) (s : ℂ), s ≠ 1 →
      DirichletCharacter.LFunction χ s = 0 →
      ((analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat : ENat) =
        analyticOrderAt (DirichletCharacter.LFunction χ) s ∧
      0 < (analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat) ∧
    ∃ iz : ∀ χ : DirichletCharacter ℂ N,
        Fintype {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
      letI (χ : DirichletCharacter ℂ N) := iz χ
      ∃ (n : ℕ) (e : (Σ χ : DirichletCharacter ℂ N,
        Σ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
          Fin ((analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat)) ≃ Fin n),
        n = ∑ χ : DirichletCharacter ℂ N,
          ∑ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
            (analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat ∧
        ∀ w : DirichletCharacter ℂ N → ℂ → ℝ,
          (∑ i : Fin n, w (e.symm i).1 (e.symm i).2.1.val) =
          ∑ χ : DirichletCharacter ℂ N,
            ∑ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
              ((analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat : ℝ) *
                w χ z.val := by
  classical
  refine ⟨fun χ => GoldbachZeroMultiset.compact_proper_zeros_finite χ K hK,
    fun χ s hs hz => GoldbachZeroMultiset.proper_zero_multiplicity χ s hs hz,?_⟩
  let Z (χ : DirichletCharacter ℂ N) :=
    {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}
  let iz : ∀ χ : DirichletCharacter ℂ N, Fintype (Z χ) :=
    fun χ => (GoldbachZeroMultiset.compact_proper_zeros_finite χ K hK).fintype
  letI (χ : DirichletCharacter ℂ N) : Fintype (Z χ) := iz χ
  let Copies := Σ χ : DirichletCharacter ℂ N,
    Σ z : Z χ, Fin ((analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat)
  letI : Fintype Copies := inferInstance
  refine ⟨iz, Fintype.card Copies, Fintype.equivFin Copies, ?_, ?_⟩
  · simp [Copies, Fintype.card_sigma]
    congr
  · intro w
    have he := (Fintype.equivFin Copies).symm.sum_comp
      (fun a : Copies => w a.1 a.2.1.val)
    rw [he]
    simp [Copies, Fintype.sum_sigma]
    congr

#print axioms solution
