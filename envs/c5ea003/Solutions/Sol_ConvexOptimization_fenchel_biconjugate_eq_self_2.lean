-- Prove2me | solution 2 for ConvexOptimization.fenchel_biconjugate_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T15:14:24.008292+00:00
-- url     : https://prove2.me/submissions/60383413-5712-40d6-a3e5-352bdffbfdd8

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_fenchelBiconjugate

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace FenchelAux

theorem strict_combo {t₁ t₂ p₁ p₂ q₁ q₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₁ + t₂ = 1) (h₁ : p₁ < q₁) (h₂ : p₂ < q₂) :
    t₁ * p₁ + t₂ * p₂ < t₁ * q₁ + t₂ * q₂ := by
  rcases eq_or_lt_of_le ht₁ with h | h
  · have ht2 : t₂ = 1 := by linarith
    rw [← h, ht2]; simpa using h₂
  · linarith [mul_lt_mul_of_pos_left h₁ h, mul_le_mul_of_nonneg_left h₂.le ht₂]

/-- **Existence of a subgradient.** A finite convex function on `ℝⁿ` is continuous,
so its strict epigraph is open and a supporting hyperplane at `(x, f x)` exists;
the hyperplane is non-vertical, and its slope is a subgradient. -/
theorem exists_subgradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y : EuclideanSpace ℝ (Fin n), ∀ z, f x + ⟪y, z - x⟫ ≤ f z := by
  have hcont : Continuous f := hf.locallyLipschitz.continuous
  set U : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | f p.1 < p.2} with hUdef
  have hUopen : IsOpen U := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hUconv : Convex ℝ U := by
    rintro ⟨z₁, t₁⟩ h₁ ⟨z₂, t₂⟩ h₂ a b ha hb hab
    simp only [hUdef, Set.mem_setOf_eq] at h₁ h₂
    have hj := hf.2 (Set.mem_univ z₁) (Set.mem_univ z₂) ha hb hab
    simp only [smul_eq_mul] at hj
    have hstrict := strict_combo ha hb hab h₁ h₂
    simp only [hUdef, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    linarith
  have hxU : ((x, f x) : EuclideanSpace ℝ (Fin n) × ℝ) ∉ U := by
    simp [hUdef]
  obtain ⟨Φ, hΦ⟩ := geometric_hahn_banach_open_point hUconv hUopen hxU
  -- Decompose the separating functional into a vector part and a slope.
  set μ : ℝ := Φ (0, 1) with hμdef
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    Φ.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ) with hLdef
  set w : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ _).symm L with hwdef
  have hw : ∀ u, ⟪w, u⟫ = Φ (u, 0) := by
    intro u
    rw [hwdef, InnerProductSpace.toDual_symm_apply]
    rfl
  have hdec : ∀ (u : EuclideanSpace ℝ (Fin n)) (t : ℝ), Φ (u, t) = ⟪w, u⟫ + t * μ := by
    intro u t
    have hsplit : ((u, t) : EuclideanSpace ℝ (Fin n) × ℝ)
        = (u, 0) + t • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
      simp [Prod.ext_iff]
    rw [hsplit, map_add, map_smul, hw u, smul_eq_mul, hμdef]
  set K : ℝ := ⟪w, x⟫ + f x * μ with hKdef
  have hlt : ∀ (z : EuclideanSpace ℝ (Fin n)) (t : ℝ), f z < t → ⟪w, z⟫ + t * μ < K := by
    intro z t ht
    have hmem : ((z, t) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ U := ht
    have h := hΦ (z, t) hmem
    rw [hdec, hdec] at h
    exact h
  -- The hyperplane is not vertical.
  have hμneg : μ < 0 := by
    have h1 := hlt x (f x + 1) (by linarith)
    rw [hKdef] at h1
    nlinarith [h1]
  have hμne : μ ≠ 0 := ne_of_lt hμneg
  -- Pass to the limit `t ↓ f z`.
  have hle : ∀ z, ⟪w, z⟫ + f z * μ ≤ K := by
    intro z
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : 0 < ε / (-μ) := div_pos hε (by linarith)
    have h1 := hlt z (f z + ε / (-μ)) (by linarith)
    have he : (f z + ε / (-μ)) * μ = f z * μ - ε := by
      field_simp
      ring
    rw [he] at h1
    linarith
  refine ⟨(-(1 / μ)) • w, fun z => ?_⟩
  have h := hle z
  rw [hKdef] at h
  have h' : ⟪w, z⟫ - ⟪w, x⟫ ≤ (f x - f z) * μ := by nlinarith [h]
  have hposc : 0 < -(1 / μ) := by
    rw [neg_pos]
    exact div_neg_of_pos_of_neg one_pos hμneg
  have hmul := mul_le_mul_of_nonneg_left h' hposc.le
  have hsimp : -(1 / μ) * ((f x - f z) * μ) = f z - f x := by
    field_simp
    ring
  rw [hsimp] at hmul
  rw [real_inner_smul_left, inner_sub_right]
  linarith

end FenchelAux

open ConvexOptimization in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    fenchelBiconjugate f x = (f x : EReal) := by
  refine le_antisymm ?_ ?_
  · -- `f** ≤ f`: the conjugate already dominates the value of the affine minorant at `x`.
    refine iSup_le fun y => ?_
    have hge : ((⟪x, y⟫ - f x : ℝ) : EReal) ≤ fenchelConjugate f y :=
      le_iSup (fun z : EuclideanSpace ℝ (Fin n) => ((⟪z, y⟫ - f z : ℝ) : EReal)) x
    calc ((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y
        ≤ ((⟪x, y⟫ : ℝ) : EReal) - ((⟪x, y⟫ - f x : ℝ) : EReal) := EReal.sub_le_sub le_rfl hge
      _ = (f x : EReal) := by
          rw [← EReal.coe_sub]
          norm_num
  · -- `f ≤ f**`: a subgradient at `x` is a maximizer.
    obtain ⟨y, hy⟩ := FenchelAux.exists_subgradient f hf x
    have hconj : fenchelConjugate f y ≤ ((⟪x, y⟫ - f x : ℝ) : EReal) := by
      refine iSup_le fun z => ?_
      have h := hy z
      rw [inner_sub_right] at h
      have hzy : ⟪z, y⟫ = ⟪y, z⟫ := real_inner_comm y z
      have hxy : ⟪x, y⟫ = ⟪y, x⟫ := real_inner_comm y x
      have hreal : ⟪z, y⟫ - f z ≤ ⟪x, y⟫ - f x := by rw [hzy, hxy]; linarith
      exact_mod_cast hreal
    calc (f x : EReal)
        = ((⟪x, y⟫ : ℝ) : EReal) - ((⟪x, y⟫ - f x : ℝ) : EReal) := by
          rw [← EReal.coe_sub]
          norm_num
      _ ≤ ((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y := EReal.sub_le_sub le_rfl hconj
      _ ≤ fenchelBiconjugate f x :=
          le_iSup (fun y : EuclideanSpace ℝ (Fin n) =>
            ((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y) y
