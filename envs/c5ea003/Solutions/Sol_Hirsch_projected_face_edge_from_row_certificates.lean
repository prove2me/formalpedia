-- Prove2me | solution 1 for Hirsch.projected_face_edge_from_row_certificates
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T15:34:21.502915+00:00
-- url     : https://prove2.me/submissions/f4fd4d09-ef80-458c-b298-94365846f15e

import Mathlib

open Set
open scoped BigOperators

namespace Hirsch.ProjectedFaceEdge

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A supporting maximum slice is an actual extreme subset. -/
lemma support_extreme (P : Set F) (f : F →ₗ[ℝ] ℝ) (β : ℝ)
    (hb : ∀ z ∈ P, f z ≤ β) :
    IsExtreme ℝ P {z | z ∈ P ∧ f z = β} := by
  refine ⟨fun z hz => hz.1, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  obtain ⟨a,b,ha,hb',hab,he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  have heq : a * f x + b * f y = β := he'.trans hz.2
  by_contra hne
  have hlt : f x < β := lt_of_le_of_ne (hb x hx) hne
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left (hb y hy) hb'.le
  have hsum : a * β + b * β = β := by rw [← add_mul, hab, one_mul]
  linarith

/-- Standard-basis comparison is sufficient for a finite linear-map identity. -/
lemma basis_ext {d : ℕ} (A B : (Fin d → ℝ) →ₗ[ℝ] F)
    (h : ∀ i, A (Pi.single i (1 : ℝ)) = B (Pi.single i (1 : ℝ))) : A = B := by
  classical
  apply LinearMap.ext
  intro x
  have hx : (∑ i : Fin d, x i • Pi.single i (1 : ℝ)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    A x = A (∑ i : Fin d, x i • Pi.single i (1 : ℝ)) := congrArg A hx.symm
    _ = ∑ i : Fin d, x i • A (Pi.single i (1 : ℝ)) := by simp only [map_sum, map_smul]
    _ = ∑ i : Fin d, x i • B (Pi.single i (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h i]
    _ = B (∑ i : Fin d, x i • Pi.single i (1 : ℝ)) := by simp only [map_sum, map_smul]
    _ = B x := congrArg B hx

/-- The rank-one image identity is checked only on finitely many columns. -/
lemma quotient_identity {d r : ℕ}
    (a : Fin r → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (G : (Fin d → ℝ) →ₗ[ℝ] F) (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (v : F) (w : Fin r → F)
    (hcol : ∀ i, G (Pi.single i (1 : ℝ)) =
      φ (Pi.single i (1 : ℝ)) • v + ∑ j, a j (Pi.single i (1 : ℝ)) • w j) :
    ∀ z, G z = φ z • v + ∑ j, a j z • w j := by
  let T : (Fin d → ℝ) →ₗ[ℝ] F :=
    { toFun := fun z => φ z • v + ∑ j, a j z • w j
      map_add' := by
        intro x y
        simp only [map_add, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro c z
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul,
          smul_add, Finset.smul_sum] }
  have hGT : G = T := basis_ext G T hcol
  intro z
  exact congrArg (fun A : (Fin d → ℝ) →ₗ[ℝ] F => A z) hGT

/-- Nonnegative original-row weights plus unrestricted equality-row weights
bound a functional on the selected face. No optimization oracle is used. -/
lemma row_bound {m r : ℕ}
    (a : Fin m → E →ₗ[ℝ] ℝ) (b : Fin m → ℝ) (row : Fin r → Fin m)
    (u : Fin m → ℝ) (g : Fin r → ℝ) (hu : ∀ i, 0 ≤ u i)
    (z : E) (hz : ∀ i, a i z ≤ b i) (hJ : ∀ j, a (row j) z = b (row j)) :
    (∑ i, u i * a i z) + (∑ j, g j * a (row j) z) ≤
      (∑ i, u i * b i) + (∑ j, g j * b (row j)) := by
  have h₁ := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hz i) (hu i))
  have h₂ : (∑ j, g j * a (row j) z) = ∑ j, g j * b (row j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hJ j]
  rw [h₂]
  exact add_le_add h₁ le_rfl

/-- The ENTIRE exposed image slice is a nondegenerate segment. The full
preimage face may have arbitrary dimension or unbounded fibres. The source
endpoints are not assumed vertices, and source adjacency is not an input. -/
theorem exposed_image_segment {d p m r : ℕ}
    (a : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (G : (Fin d → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (f : (Fin p → ℝ) →ₗ[ℝ] ℝ) (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (row : Fin r → Fin m) (lam : Fin r → ℝ) (w : Fin r → (Fin p → ℝ))
    (lower upper : Fin m → ℝ) (lowerEq upperEq : Fin r → ℝ)
    (x y : Fin d → ℝ)
    (hx : ∀ i, a i x ≤ b i) (hy : ∀ i, a i y ≤ b i)
    (hxJ : ∀ j, a (row j) x = b (row j)) (hyJ : ∀ j, a (row j) y = b (row j))
    (hne : G x ≠ G y) (hφ : φ y - φ x = 1)
    (hlam : ∀ j, 0 < lam j)
    (hexpose : f.comp G = ∑ j, lam j • a (row j))
    (hline : ∀ i, G (Pi.single i (1 : ℝ)) =
      φ (Pi.single i (1 : ℝ)) • (G y - G x) +
        ∑ j, a (row j) (Pi.single i (1 : ℝ)) • w j)
    (hlower : ∀ i, 0 ≤ lower i) (hupper : ∀ i, 0 ≤ upper i)
    (hlform : -φ = (∑ i, lower i • a i) + ∑ j, lowerEq j • a (row j))
    (huform : φ = (∑ i, upper i • a i) + ∑ j, upperEq j • a (row j))
    (hlsharp : -φ x = (∑ i, lower i * b i) + ∑ j, lowerEq j * b (row j))
    (husharp : φ y = (∑ i, upper i * b i) + ∑ j, upperEq j * b (row j)) :
    let P := {z : Fin d → ℝ | ∀ i, a i z ≤ b i}
    let β := ∑ j, lam j * b (row j)
    (∀ z ∈ G '' P, f z ≤ β) ∧
      {z | z ∈ G '' P ∧ f z = β} = segment ℝ (G x) (G y) ∧
      G x ≠ G y ∧ IsExtreme ℝ (G '' P) (segment ℝ (G x) (G y)) := by
  classical
  let P := {z : Fin d → ℝ | ∀ i, a i z ≤ b i}
  let β : ℝ := ∑ j, lam j * b (row j)
  have hnormal (z : Fin d → ℝ) : f (G z) = ∑ j, lam j * a (row j) z := by
    have h := congrArg (fun T : (Fin d → ℝ) →ₗ[ℝ] ℝ => T z) hexpose
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] using h
  have hglobal : ∀ z ∈ G '' P, f z ≤ β := by
    rintro z ⟨q, hq, rfl⟩
    rw [hnormal]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hq (row j)) (hlam j).le)
  have hactive (z : Fin d → ℝ) (hz : z ∈ P) (hmax : f (G z) = β) :
      ∀ j, a (row j) z = b (row j) := by
    intro j
    by_contra hneq
    have hstrict : (∑ i, lam i * a (row i) z) < ∑ i, lam i * b (row i) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_le_mul_of_nonneg_left (hz (row i)) (hlam i).le
      · exact ⟨j, Finset.mem_univ j,
          mul_lt_mul_of_pos_left (lt_of_le_of_ne (hz (row j)) hneq) (hlam j)⟩
    rw [← hnormal z] at hstrict
    exact (ne_of_lt hstrict) hmax
  have hquot := quotient_identity (fun j => a (row j)) G φ (G y - G x) w hline
  have hpoint (z : Fin d → ℝ) (hJ : ∀ j, a (row j) z = b (row j)) :
      G z = G x + (φ z - φ x) • (G y - G x) := by
    have hzline := hquot z
    have hxline := hquot x
    have hzsum : (∑ j, a (row j) z • w j) = ∑ j, b (row j) • w j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hJ j]
    have hxsum : (∑ j, a (row j) x • w j) = ∑ j, b (row j) • w j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hxJ j]
    rw [hzsum] at hzline
    rw [hxsum] at hxline
    calc
      G z = φ z • (G y - G x) + ∑ j, b (row j) • w j := hzline
      _ = (φ x • (G y - G x) + ∑ j, b (row j) • w j) +
          (φ z - φ x) • (G y - G x) := by rw [sub_smul]; abel
      _ = G x + (φ z - φ x) • (G y - G x) := by rw [← hxline]
  have hbetween (z : Fin d → ℝ) (hz : z ∈ P)
      (hJ : ∀ j, a (row j) z = b (row j)) : φ x ≤ φ z ∧ φ z ≤ φ y := by
    have hl := congrArg (fun T : (Fin d → ℝ) →ₗ[ℝ] ℝ => T z) hlform
    have hu := congrArg (fun T : (Fin d → ℝ) →ₗ[ℝ] ℝ => T z) huform
    simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] at hl hu
    have hlow := row_bound a b row lower lowerEq hlower z hz hJ
    have hupp := row_bound a b row upper upperEq hupper z hz hJ
    rw [← hl, ← hlsharp] at hlow
    rw [← hu, ← husharp] at hupp
    exact ⟨by linarith, hupp⟩
  have hface : {z | z ∈ G '' P ∧ f z = β} = segment ℝ (G x) (G y) := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨q, hq, hqz⟩, hz⟩
      subst z
      have hJ := hactive q hq hz
      have hb := hbetween q hq hJ
      let s : ℝ := φ q - φ x
      have hs0 : 0 ≤ s := sub_nonneg.mpr hb.1
      have hs1 : s ≤ 1 := by dsimp only [s]; linarith [hb.2, hφ]
      refine ⟨1 - s, s, sub_nonneg.mpr hs1, hs0, by ring, ?_⟩
      rw [hpoint q hJ]
      change (1 - s) • G x + s • G y = G x + s • (G y - G x)
      rw [sub_smul, one_smul, smul_sub]
      abel
    · rintro z ⟨s,t,hs,ht,hst,hcomb⟩
      let q : Fin d → ℝ := s • x + t • y
      have hq : q ∈ P := by
        intro i
        change a i (s • x + t • y) ≤ b i
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h₁ := mul_le_mul_of_nonneg_left (hx i) hs
        have h₂ := mul_le_mul_of_nonneg_left (hy i) ht
        have he : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
        linarith
      have hGq : G q = z := by
        dsimp only [q]
        rw [map_add, map_smul, map_smul]
        exact hcomb
      have hqJ : ∀ j, a (row j) q = b (row j) := by
        intro j
        dsimp only [q]
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
          hxJ j, hyJ j, ← add_mul, hst, one_mul]
      refine ⟨⟨q, hq, hGq⟩, ?_⟩
      rw [← hGq, hnormal]
      exact Finset.sum_congr rfl (fun j _ => by rw [hqJ j])
  refine ⟨hglobal, hface, hne, ?_⟩
  rw [← hface]
  exact support_extreme (G '' P) f β hglobal

end Hirsch.ProjectedFaceEdge

/-- Finite original-row certificates imply a genuine ordinary edge in a linear
image, without assuming source adjacency, bounded fibres or a supplied face. -/
theorem solution {d p m r : ℕ}
    (a : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (G : (Fin d → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (f : (Fin p → ℝ) →ₗ[ℝ] ℝ) (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (row : Fin r → Fin m) (lam : Fin r → ℝ) (w : Fin r → (Fin p → ℝ))
    (lower upper : Fin m → ℝ) (lowerEq upperEq : Fin r → ℝ)
    (x y : Fin d → ℝ)
    (hx : ∀ i, a i x ≤ b i) (hy : ∀ i, a i y ≤ b i)
    (hxJ : ∀ j, a (row j) x = b (row j)) (hyJ : ∀ j, a (row j) y = b (row j))
    (hne : G x ≠ G y) (hφ : φ y - φ x = 1)
    (hlam : ∀ j, 0 < lam j)
    (hexpose : f.comp G = ∑ j, lam j • a (row j))
    (hline : ∀ i, G (Pi.single i (1 : ℝ)) =
      φ (Pi.single i (1 : ℝ)) • (G y - G x) +
        ∑ j, a (row j) (Pi.single i (1 : ℝ)) • w j)
    (hlower : ∀ i, 0 ≤ lower i) (hupper : ∀ i, 0 ≤ upper i)
    (hlform : -φ = (∑ i, lower i • a i) + ∑ j, lowerEq j • a (row j))
    (huform : φ = (∑ i, upper i • a i) + ∑ j, upperEq j • a (row j))
    (hlsharp : -φ x = (∑ i, lower i * b i) + ∑ j, lowerEq j * b (row j))
    (husharp : φ y = (∑ i, upper i * b i) + ∑ j, upperEq j * b (row j)) :
    let P := {z : Fin d → ℝ | ∀ i, a i z ≤ b i}
    let β := ∑ j, lam j * b (row j)
    (∀ z ∈ G '' P, f z ≤ β) ∧
      {z | z ∈ G '' P ∧ f z = β} = segment ℝ (G x) (G y) ∧
      G x ≠ G y ∧ IsExtreme ℝ (G '' P) (segment ℝ (G x) (G y)) := by
  exact Hirsch.ProjectedFaceEdge.exposed_image_segment a b G f φ row lam w lower upper
    lowerEq upperEq x y hx hy hxJ hyJ hne hφ hlam hexpose hline hlower hupper
    hlform huform hlsharp husharp

#print axioms Hirsch.ProjectedFaceEdge.quotient_identity
#print axioms Hirsch.ProjectedFaceEdge.exposed_image_segment
#print axioms solution
