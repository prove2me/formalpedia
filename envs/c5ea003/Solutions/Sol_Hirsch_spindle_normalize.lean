-- Prove2me | solution 1 for Hirsch.spindle_normalize
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T15:30:07.983842+00:00
-- url     : https://prove2.me/submissions/51ecd606-ae99-45b7-8fd2-e529b0fed9cf

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

variable {d n : ℕ}

lemma u_ne_v_of_hlong
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)}
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    u ≠ v := by
  intro h
  exact (hlong (fun _ => u) ⟨rfl, h.symm ▸ rfl, fun _ _ => Or.inl rfl⟩).elim

lemma inner_single_one (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    ⟪EuclideanSpace.single j (1 : ℝ), y⟫ = y j := by
  simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) j (1 : ℝ) y

def evalCoord (k : Fin d) : EuclideanSpace ℝ (Fin d) →+ ℝ where
  toFun x := x k
  map_zero' := by
    simp [PiLp.zero_apply]
  map_add' x y := by
    simp [PiLp.add_apply]

lemma euclid_sum_apply (k : Fin d) {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin d)) :
    (∑ i, f i) k = ∑ i, f i k :=
  map_sum (evalCoord k) f Finset.univ

lemma inner_mapped (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (a y : EuclideanSpace ℝ (Fin d)) :
    ⟪∑ j : Fin d,
        ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ •
          EuclideanSpace.single j (1 : ℝ), y⟫ =
      ⟪a, T.symm y⟫ := by
  have hsum :
      ⟪∑ j : Fin d,
          ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ •
            EuclideanSpace.single j (1 : ℝ), y⟫ =
        ∑ j : Fin d,
          ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ * y j := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_single_one]
    simp
  have hy : (∑ j : Fin d, y j • EuclideanSpace.single j (1 : ℝ)) = y := by
    ext k
    rw [euclid_sum_apply]
    simp [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, Finset.sum_ite_eq]
  have hlin :
      ∑ j : Fin d, y j • T.symm (EuclideanSpace.single j (1 : ℝ)) =
        T.symm y := by
    have := congrArg T.symm hy.symm
    simpa [map_sum, map_smul] using this.symm
  calc
    ⟪∑ j : Fin d,
        ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ •
          EuclideanSpace.single j (1 : ℝ), y⟫
        = ∑ j : Fin d, ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ * y j := hsum
    _ = ∑ j : Fin d, y j * ⟪a, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ := by
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ⟪a, ∑ j : Fin d, y j • T.symm (EuclideanSpace.single j (1 : ℝ))⟫ := by
          rw [inner_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [inner_smul_right]
    _ = ⟪a, T.symm y⟫ := by rw [hlin]

def mappedA (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    Fin n → EuclideanSpace ℝ (Fin d) :=
  fun i => ∑ j : Fin d,
    ⟪a i, T.symm (EuclideanSpace.single j (1 : ℝ))⟫ •
      EuclideanSpace.single j (1 : ℝ)

def mappedB (m : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => b i - ⟪a i, m⟫

lemma mem_mappedHpoly (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    y ∈ Hpoly (mappedA T a) (mappedB m a b) ↔
      T.symm y + m ∈ Hpoly a b := by
  simp only [Hpoly, mem_setOf_eq, mappedA, mappedB]
  constructor
  · intro hy i
    have hin := inner_mapped T (a i) y
    have : ⟪a i, T.symm y + m⟫ = ⟪a i, T.symm y⟫ + ⟪a i, m⟫ := by
      simp [inner_add_right]
    linarith [hy i]
  · intro hx i
    have hin := inner_mapped T (a i) y
    have : ⟪a i, T.symm y + m⟫ = ⟪a i, T.symm y⟫ + ⟪a i, m⟫ := by
      simp [inner_add_right]
    linarith [hx i]

lemma hpoly_eq_image (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Hpoly (mappedA T a) (mappedB m a b) =
      (fun z => T (z - m)) '' Hpoly a b := by
  ext y
  constructor
  · intro hy
    refine ⟨T.symm y + m, (mem_mappedHpoly T m a b y).1 hy, ?_⟩
    simp
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (mem_mappedHpoly T m a b (T (x - m))).2 (by simpa using hx)

lemma sub_affine_combo (p q : ℝ) (hpq : p + q = 1)
    (x y m : EuclideanSpace ℝ (Fin d)) :
    p • x + q • y - m = p • (x - m) + q • (y - m) := by
  calc
    p • x + q • y - m
        = p • x + q • y - (p + q) • m := by rw [hpq, one_smul]
    _ = p • x + q • y - (p • m + q • m) := by rw [add_smul]
    _ = (p • x - p • m) + (q • y - q • m) := by abel
    _ = p • (x - m) + q • (y - m) := by simp [smul_sub]

lemma segment_image_linear
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m x y : EuclideanSpace ℝ (Fin d)) :
    (fun z => T (z - m)) '' segment ℝ x y =
      segment ℝ (T (x - m)) (T (y - m)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    rw [← map_smul, ← map_smul, ← map_add, ← sub_affine_combo p q hpq]
  · intro hz
    obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hz
    refine ⟨p • x + q • y, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    rw [← hcomb, ← map_smul, ← map_smul, ← map_add, ← sub_affine_combo p q hpq]

lemma openSegment_image_linear
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m x y : EuclideanSpace ℝ (Fin d)) :
    (fun z => T (z - m)) '' openSegment ℝ x y =
      openSegment ℝ (T (x - m)) (T (y - m)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    rw [← map_smul, ← map_smul, ← map_add, ← sub_affine_combo p q hpq]
  · intro hz
    obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hz
    refine ⟨p • x + q • y, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    rw [← hcomb, ← map_smul, ← map_smul, ← map_add, ← sub_affine_combo p q hpq]

lemma isExtreme_image_segment
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    {P : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hex : IsExtreme ℝ P (segment ℝ x y)) :
    IsExtreme ℝ ((fun z => T (z - m)) '' P)
      (segment ℝ (T (x - m)) (T (y - m))) := by
  constructor
  · intro z hz
    have hz' : z ∈ (fun w => T (w - m)) '' segment ℝ x y := by
      rwa [segment_image_linear]
    rcases hz' with ⟨w, hw, rfl⟩
    exact ⟨w, hex.subset hw, rfl⟩
  · intro X hX Y hY Z hZ hopen
    rcases hX with ⟨x1, hx1, rfl⟩
    rcases hY with ⟨x2, hx2, rfl⟩
    have hZim : Z ∈ (fun w => T (w - m)) '' segment ℝ x y := by
      rwa [segment_image_linear]
    rcases hZim with ⟨z, hzseg, rfl⟩
    have hopen' : T (z - m) ∈
        (fun w => T (w - m)) '' openSegment ℝ x1 x2 := by
      rwa [openSegment_image_linear]
    rcases hopen' with ⟨z', hzopen, heq⟩
    have : z' = z := by
      have := congrArg (fun t => T.symm t + m) heq
      simp at this
      exact this
    subst this
    have hx1seg : x1 ∈ segment ℝ x y :=
      hex.left_mem_of_mem_openSegment hx1 hx2 hzseg hzopen
    have : T (x1 - m) ∈ (fun w => T (w - m)) '' segment ℝ x y :=
      ⟨x1, hx1seg, rfl⟩
    rwa [segment_image_linear] at this

lemma adj_image
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    {P : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)} :
    Adj ((fun z => T (z - m)) '' P) (T (x - m)) (T (y - m)) ↔ Adj P x y := by
  constructor
  · intro h
    obtain ⟨hne, hex⟩ := h
    have hne' : x ≠ y := fun hxy => hne (by simp [hxy])
    -- Inverse affine map: w ↦ T.symm (w + T m) = T.symm w + m
    -- = T.symm (w - (-T m))
    have hex' :=
      isExtreme_image_segment T.symm (-T m) (P := (fun z => T (z - m)) '' P)
        (x := T (x - m)) (y := T (y - m)) hex
    have himP :
        (fun w => T.symm (w - -T m)) '' ((fun z => T (z - m)) '' P) = P := by
      ext p
      constructor
      · intro hp
        rcases hp with ⟨_, ⟨p', hp', rfl⟩, rfl⟩
        simpa using hp'
      · intro hp
        refine ⟨T (p - m), ⟨p, hp, rfl⟩, ?_⟩
        simp
    have hxeq : T.symm (T (x - m) - -T m) = x := by simp
    have hyeq : T.symm (T (y - m) - -T m) = y := by simp
    rw [himP, hxeq, hyeq] at hex'
    exact ⟨hne', hex'⟩
  · intro h
    obtain ⟨hne, hex⟩ := h
    refine ⟨?_, isExtreme_image_segment T m hex⟩
    intro heq
    exact hne (T.injective (by simpa using heq))

lemma extreme_image
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    {P : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    T (x - m) ∈ extremePoints ℝ ((fun z => T (z - m)) '' P) ↔
      x ∈ extremePoints ℝ P := by
  constructor
  · intro hx
    have hxP : x ∈ P := by
      rcases hx.1 with ⟨x', hx', heq⟩
      have : x' = x := T.injective (by simpa using heq)
      simpa [this] using hx'
    refine ⟨hxP, ?_⟩
    intro x1 hx1 x2 hx2 hop
    have hop' : T (x - m) ∈ openSegment ℝ (T (x1 - m)) (T (x2 - m)) := by
      have : T (x - m) ∈ (fun z => T (z - m)) '' openSegment ℝ x1 x2 :=
        ⟨x, hop, rfl⟩
      rwa [openSegment_image_linear] at this
    have := hx.2 ⟨x1, hx1, rfl⟩ ⟨x2, hx2, rfl⟩ hop'
    exact T.injective (by simpa using this)
  · intro hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    intro y1 hy1 y2 hy2 hop
    rcases hy1 with ⟨x1, hx1, rfl⟩
    rcases hy2 with ⟨x2, hx2, rfl⟩
    have hop' : x ∈ openSegment ℝ x1 x2 := by
      have : T (x - m) ∈ (fun z => T (z - m)) '' openSegment ℝ x1 x2 := by
        rwa [openSegment_image_linear]
      rcases this with ⟨z, hz, heq⟩
      have : z = x := T.injective (by simpa using heq)
      simpa [this] using hz
    have := hx.2 hx1 hx2 hop'
    simp [this]

noncomputable def permCoords (e : Equiv.Perm (Fin d)) :
    EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  let φ := WithLp.linearEquiv (p := 2) (K := ℝ) (V := Fin d → ℝ)
  φ.trans ((LinearEquiv.piCongrLeft' ℝ (fun _ : Fin d => ℝ) e).trans φ.symm)

noncomputable def shearForward (w evec : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.id + (⟪w, w⟫)⁻¹ • (innerₛₗ ℝ w).smulRight (evec - w)

noncomputable def shearBackward (w evec : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.id - (⟪evec, w⟫)⁻¹ • (innerₛₗ ℝ w).smulRight (evec - w)

lemma shearForward_apply (w evec x : EuclideanSpace ℝ (Fin d)) :
    shearForward w evec x =
      x + (⟪w, w⟫)⁻¹ • ⟪w, x⟫ • (evec - w) := by
  simp [shearForward, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]

lemma shearBackward_apply (w evec x : EuclideanSpace ℝ (Fin d)) :
    shearBackward w evec x =
      x - (⟪evec, w⟫)⁻¹ • ⟪w, x⟫ • (evec - w) := by
  simp [shearBackward, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]

lemma shearForward_w (w evec : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    shearForward w evec w = evec := by
  have hnn : ⟪w, w⟫ ≠ 0 := inner_self_eq_zero.not.mpr hw
  rw [shearForward_apply, smul_smul, inv_mul_cancel₀ hnn, one_smul]
  abel

lemma inner_shearBackward (w evec x : EuclideanSpace ℝ (Fin d))
    (he : ⟪evec, w⟫ ≠ 0) :
    ⟪w, shearBackward w evec x⟫ = ⟪w, x⟫ * ⟪w, w⟫ * (⟪evec, w⟫)⁻¹ := by
  have hβ : ⟪w, evec - w⟫ = ⟪evec, w⟫ - ⟪w, w⟫ := by
    rw [inner_sub_right, real_inner_comm w evec]
  rw [shearBackward_apply, inner_sub_right, inner_smul_right, inner_smul_right, hβ]
  field_simp [he]
  ring

lemma inner_shearForward (w evec x : EuclideanSpace ℝ (Fin d))
    (hnn : ⟪w, w⟫ ≠ 0) :
    ⟪w, shearForward w evec x⟫ = ⟪w, x⟫ * ⟪evec, w⟫ * (⟪w, w⟫)⁻¹ := by
  have hβ : ⟪w, evec - w⟫ = ⟪evec, w⟫ - ⟪w, w⟫ := by
    rw [inner_sub_right, real_inner_comm w evec]
  rw [shearForward_apply, inner_add_right, inner_smul_right, inner_smul_right, hβ]
  field_simp [hnn]
  ring

lemma shear_smul_cancel_forward (w evec x : EuclideanSpace ℝ (Fin d))
    (hnn : ⟪w, w⟫ ≠ 0) (he : ⟪evec, w⟫ ≠ 0) :
    (⟪w, w⟫)⁻¹ • (⟪w, x⟫ * ⟪w, w⟫ * (⟪evec, w⟫)⁻¹) • (evec - w) =
      (⟪evec, w⟫)⁻¹ • ⟪w, x⟫ • (evec - w) := by
  rw [smul_smul, smul_smul]
  congr 1
  field_simp [hnn, he]

lemma shear_smul_cancel_backward (w evec x : EuclideanSpace ℝ (Fin d))
    (hnn : ⟪w, w⟫ ≠ 0) (he : ⟪evec, w⟫ ≠ 0) :
    (⟪evec, w⟫)⁻¹ • (⟪w, x⟫ * ⟪evec, w⟫ * (⟪w, w⟫)⁻¹) • (evec - w) =
      (⟪w, w⟫)⁻¹ • ⟪w, x⟫ • (evec - w) := by
  rw [smul_smul, smul_smul]
  congr 1
  field_simp [hnn, he]

lemma shear_comp (w evec : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) (he : ⟪evec, w⟫ ≠ 0) :
    shearForward w evec ∘ₗ shearBackward w evec = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hnn : ⟪w, w⟫ ≠ 0 := inner_self_eq_zero.not.mpr hw
  rw [LinearMap.comp_apply, LinearMap.id_apply, shearForward_apply]
  rw [inner_shearBackward w evec x he]
  rw [shearBackward_apply]
  rw [shear_smul_cancel_forward w evec x hnn he]
  abel

lemma shear_comp' (w evec : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) (he : ⟪evec, w⟫ ≠ 0) :
    shearBackward w evec ∘ₗ shearForward w evec = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hnn : ⟪w, w⟫ ≠ 0 := inner_self_eq_zero.not.mpr hw
  rw [LinearMap.comp_apply, LinearMap.id_apply, shearBackward_apply]
  rw [inner_shearForward w evec x hnn]
  rw [shearForward_apply]
  rw [shear_smul_cancel_backward w evec x hnn he]
  abel

noncomputable def shearEquiv (w evec : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) (he : ⟪evec, w⟫ ≠ 0) :
    EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearEquiv.ofLinear (shearForward w evec) (shearBackward w evec)
    (shear_comp w evec hw he) (shear_comp' w evec hw he)

lemma shearEquiv_apply (w evec : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) (he : ⟪evec, w⟫ ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    shearEquiv w evec hw he x = shearForward w evec x :=
  rfl

lemma permCoords_apply (e : Equiv.Perm (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    permCoords e x j = x (e.symm j) := by
  simp [permCoords, LinearEquiv.trans_apply]

lemma tightness_mapped (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    ⟪mappedA T a i, T (x - m)⟫ = mappedB m a b i ↔ ⟪a i, x⟫ = b i := by
  have hin : ⟪mappedA T a i, T (x - m)⟫ = ⟪a i, x - m⟫ := by
    simpa [mappedA] using inner_mapped T (a i) (T (x - m))
  have hsub : ⟪a i, x - m⟫ = ⟪a i, x⟫ - ⟪a i, m⟫ := inner_sub_right _ _ _
  constructor
  · intro h
    have h' : ⟪a i, x - m⟫ = mappedB m a b i := hin.symm.trans h
    rw [hsub, mappedB] at h'
    linarith
  · intro h
    have h' : ⟪mappedA T a i, T (x - m)⟫ = ⟪a i, x⟫ - ⟪a i, m⟫ :=
      hin.trans hsub
    rw [h']
    simp [mappedB, h]

lemma affine_image_bounded
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d))
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Bornology.IsBounded s) :
    Bornology.IsBounded ((fun z => T (z - m)) '' s) := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  have hsub : s ⊆ Metric.closedBall 0 C := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hC x hx
  have hK : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) C) :=
    isCompact_closedBall _ _
  have hT : Continuous (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    LinearMap.continuous_of_finiteDimensional
      (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  have hf : Continuous (fun z : EuclideanSpace ℝ (Fin d) => T (z - m)) :=
    hT.comp (continuous_id.sub continuous_const)
  have himg : IsCompact ((fun z => T (z - m)) '' Metric.closedBall 0 C) :=
    hK.image hf
  exact himg.isBounded.subset (image_mono hsub)

lemma exists_nonzero_coord {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) :
    ∃ k : Fin d, w k ≠ 0 := by
  by_contra h
  push Not at h
  have : w = 0 := by
    ext i
    exact h i
  exact hw this

lemma single_neg_one (j : Fin d) :
    EuclideanSpace.single j (-1 : ℝ) = -EuclideanSpace.single j (1 : ℝ) := by
  ext i
  simp [PiLp.single_apply, PiLp.neg_apply]
  split_ifs <;> ring

theorem solution (d n : ℕ) (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin n → EuclideanSpace ℝ (Fin d)) (b' : Fin n → ℝ),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b' i) ∧
      (∀ i, ⟪a i, u⟫ = b i ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
        ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
            w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
            ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a' b') (w j) (w (j + 1))) := by
  let lastIdx : Fin d := ⟨d - 1, Nat.sub_lt hd (by decide)⟩
  let m : EuclideanSpace ℝ (Fin d) := midpoint ℝ u v
  have hu_ne_v : u ≠ v := u_ne_v_of_hlong hlong
  let wvec : EuclideanSpace ℝ (Fin d) := u - m
  have hw : wvec ≠ 0 := by
    intro h0
    have hu_eq : u = m := sub_eq_zero.mp h0
    have : midpoint ℝ u v = u := hu_eq.symm
    exact hu_ne_v ((midpoint_eq_left_iff (R := ℝ)).1 this)
  have hvm : v - m = -wvec := by
    dsimp [wvec, m]
    rw [right_sub_midpoint, left_sub_midpoint, smul_sub, smul_sub]
    abel
  obtain ⟨k, hk⟩ := exists_nonzero_coord hw
  let e : Equiv.Perm (Fin d) := Equiv.swap k lastIdx
  let wperm : EuclideanSpace ℝ (Fin d) := permCoords e wvec
  have hwperm : wperm ≠ 0 := by
    intro h0
    have : wvec = 0 := (permCoords e).injective (by simpa [wperm] using h0)
    exact hw this
  have he_inner : ⟪EuclideanSpace.single lastIdx (1 : ℝ), wperm⟫ ≠ 0 := by
    rw [inner_single_one]
    have : wperm lastIdx = wvec k := by
      simp [wperm, permCoords_apply, e, Equiv.swap_apply_right]
    simpa [this] using hk
  let S := shearEquiv wperm (EuclideanSpace.single lastIdx (1 : ℝ)) hwperm he_inner
  let T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (permCoords e).trans S
  have hTu : T wvec = EuclideanSpace.single lastIdx (1 : ℝ) := by
    change S (permCoords e wvec) = EuclideanSpace.single lastIdx (1 : ℝ)
    rw [shearEquiv_apply, shearForward_w wperm _ hwperm]
  have hTu' : T (u - m) = EuclideanSpace.single lastIdx (1 : ℝ) := hTu
  have hTv : T (v - m) = EuclideanSpace.single lastIdx (-1 : ℝ) := by
    rw [hvm, map_neg, hTu, single_neg_one]
  let a' := mappedA T a
  let b' := mappedB m a b
  have hP' : Hpoly a' b' = (fun z => T (z - m)) '' Hpoly a b :=
    hpoly_eq_image T m a b
  have hne' : (Hpoly a' b').Nonempty := by
    rw [hP']
    obtain ⟨x, hx⟩ := hne
    exact ⟨T (x - m), ⟨x, hx, rfl⟩⟩
  have hbd' : Bornology.IsBounded (Hpoly a' b') := by
    rw [hP']
    exact affine_image_bounded T m hbd
  have hu' : EuclideanSpace.single lastIdx (1 : ℝ) ∈ extremePoints ℝ (Hpoly a' b') := by
    rw [hP', ← hTu']
    exact (extreme_image T m).2 hu
  have hv' : EuclideanSpace.single lastIdx (-1 : ℝ) ∈ extremePoints ℝ (Hpoly a' b') := by
    rw [hP', ← hTv]
    exact (extreme_image T m).2 hv
  have htight : ∀ i, ⟪a i, u⟫ = b i ↔
      ⟪a' i, EuclideanSpace.single lastIdx (1 : ℝ)⟫ = b' i := by
    intro i
    have tU := tightness_mapped T m a b u i
    simpa [a', b', hTu'] using tU.symm
  have hsp' : ∀ i,
      (⟪a' i, EuclideanSpace.single lastIdx (1 : ℝ)⟫ = b' i) ↔
        ⟪a' i, EuclideanSpace.single lastIdx (-1 : ℝ)⟫ ≠ b' i := by
    intro i
    have tU := tightness_mapped T m a b u i
    have tV := tightness_mapped T m a b v i
    rw [hTu'] at tU
    rw [hTv] at tV
    constructor
    · intro h
      have hu_t : ⟪a i, u⟫ = b i := tU.mp (by simpa [a', b'] using h)
      have hv_nt := (hspindle i).mp hu_t
      intro hneg
      exact hv_nt (tV.mp (by simpa [a', b'] using hneg))
    · intro hne
      refine tU.mpr ?_
      refine (hspindle i).mpr ?_
      intro hv_t
      exact hne (by simpa [a', b'] using tV.mpr hv_t)
  have hlong' : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = EuclideanSpace.single lastIdx (1 : ℝ) ∧
          w d = EuclideanSpace.single lastIdx (-1 : ℝ) ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a' b') (w j) (w (j + 1))) := by
    intro walk hwalk
    rcases hwalk with ⟨hw0, hwd, hstep⟩
    refine hlong (fun j => T.symm (walk j) + m) ⟨?_, ?_, ?_⟩
    · have : walk 0 = T (u - m) := by rw [hw0, hTu']
      simp [this]
    · have : walk d = T (v - m) := by rw [hwd, hTv]
      simp [this]
    · intro j hj
      cases hstep j hj with
      | inl heq =>
        left
        simp [heq]
      | inr hadj =>
        right
        have hx : T ((T.symm (walk j) + m) - m) = walk j := by simp
        have hy : T ((T.symm (walk (j + 1)) + m) - m) = walk (j + 1) := by simp
        have hadj' :
            Adj (Hpoly a' b')
              (T ((T.symm (walk j) + m) - m))
              (T ((T.symm (walk (j + 1)) + m) - m)) := by
          simpa [hx, hy] using hadj
        have hiff :
            Adj (Hpoly a' b')
              (T ((T.symm (walk j) + m) - m))
              (T ((T.symm (walk (j + 1)) + m) - m)) ↔
            Adj (Hpoly a b) (T.symm (walk j) + m) (T.symm (walk (j + 1)) + m) := by
          rw [hP']
          exact adj_image T m
        exact hiff.1 hadj'
  refine ⟨a', b', hne', hbd', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lastIdx] using hu'
  · simpa [lastIdx] using hv'
  · simpa [lastIdx] using hsp'
  · simpa [lastIdx] using htight
  · simpa [lastIdx] using hlong'


