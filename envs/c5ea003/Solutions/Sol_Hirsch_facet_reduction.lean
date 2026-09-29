-- Prove2me | solution 1 for Hirsch.facet_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:42:59.391432+00:00
-- url     : https://prove2.me/submissions/d0ea5375-6c35-4963-a148-56a6a49b70b9

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Hirsch

/-!
# Facets are polyhedra of one dimension less

Charting the hyperplane that carries a facet by a linear isometry from `ℝ^(d-1)`
realises the facet of an H-polytope with `n` inequalities as an H-polyhedron in
`ℝ^(d-1)` cut out by `n-1` inequalities, with the same vertices and edges.  This
is the recursion step of Barnette--Larman and Kalai--Kleitman.
-/

namespace HirschWalk

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `Reach P L u v`: a walk of exactly `L` steps from `u` to `v`, each step either
stationary or along an edge.  This is the body of `DiamLE`. -/
def Reach (P : Set E) (L : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

end HirschWalk

namespace HirschFace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]


/-- The minimising face of a linear functional over a convex set is an extreme subset. -/
theorem exposed_isExtreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (t : ℝ)
    (hmin : ∀ x ∈ P, t ≤ f x) : IsExtreme ℝ P {x | x ∈ P ∧ f x = t} := by
  constructor
  · exact fun x hx => hx.1
  · rintro x₁ hx₁ x₂ hx₂ x ⟨hxP, hxt⟩ ⟨p, q, hp, hq, hpq, hx⟩
    have hc : f x = p * f x₁ + q * f x₂ := by
      rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hmin _ hx₁
    have h2 := hmin _ hx₂
    have h3 : p * f x₁ + q * f x₂ = t := by rw [← hc, hxt]
    have key : p * (f x₁ - t) + q * (f x₂ - t) = 0 := by linear_combination h3 - t * hpq
    have hz1 : 0 ≤ p * (f x₁ - t) := mul_nonneg hp.le (by linarith)
    have hz2 : 0 ≤ q * (f x₂ - t) := mul_nonneg hq.le (by linarith)
    refine ⟨hx₁, ?_⟩
    have : p * (f x₁ - t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hp)
    · linarith

end HirschFace

open HirschWalk HirschFace

namespace HirschFacet

variable {d n m : ℕ}

/-- Every `m`-dimensional subspace of `ℝ^d` is the range of a linear isometric
embedding of `ℝ^m`. -/
theorem exists_chart (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (m : ℕ)
    (hK : Module.finrank ℝ K = m) :
    ∃ ψ : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Set.range ψ = (K : Set (EuclideanSpace ℝ (Fin d))) := by
  subst hK
  refine ⟨K.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ K).repr.symm.toLinearIsometry, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩; exact ((stdOrthonormalBasis ℝ K).repr.symm y).2
  · intro hz
    exact ⟨(stdOrthonormalBasis ℝ K).repr ⟨z, hz⟩, by simp⟩

/-! ## Pulling the inequality data back along a chart -/

variable (ψ : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))

/-- The normal vectors seen in the chart. -/
noncomputable def pullA (a : Fin n → EuclideanSpace ℝ (Fin d)) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun j => LinearMap.adjoint ψ.toLinearMap (a j)

/-- The right-hand sides seen in the chart based at `p`. -/
noncomputable def pullB (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  fun j => b j - ⟪a j, p⟫

/-- The chart map: an affine isometric embedding of `ℝ^m` based at `p`. -/
noncomputable def chartMap (p : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d) :=
  fun y => p + ψ y

variable {ψ}

theorem pullA_inner (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (y : EuclideanSpace ℝ (Fin m)) : ⟪pullA ψ a j, y⟫ = ⟪a j, ψ y⟫ := by
  rw [pullA, LinearMap.adjoint_inner_left]
  rfl

theorem chartMap_inner (a : Fin n → EuclideanSpace ℝ (Fin d)) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin m)) :
    ⟪a j, chartMap ψ p y⟫ = ⟪a j, p⟫ + ⟪pullA ψ a j, y⟫ := by
  rw [chartMap, inner_add_right, pullA_inner]

theorem chartMap_mem_iff (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin m)) :
    chartMap ψ p y ∈ Hpoly a b ↔ y ∈ Hpoly (pullA ψ a) (pullB a b p) := by
  constructor
  · intro h j
    have := h j
    rw [chartMap_inner] at this
    simp only [pullB]
    linarith
  · intro h j
    have := h j
    simp only [pullB] at this
    rw [chartMap_inner]
    linarith

theorem chartMap_injective (p : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (chartMap ψ p) := by
  intro y z h
  simp only [chartMap, add_right_inj] at h
  exact ψ.injective h

theorem chartMap_affine (p : EuclideanSpace ℝ (Fin d)) (s t : ℝ) (hst : s + t = 1)
    (y z : EuclideanSpace ℝ (Fin m)) :
    chartMap ψ p (s • y + t • z) = s • chartMap ψ p y + t • chartMap ψ p z := by
  have hp : s • p + t • p = p := by rw [← add_smul, hst, one_smul]
  simp only [chartMap, map_add, map_smul, smul_add]
  calc p + (s • ψ y + t • ψ z)
      = (s • p + t • p) + (s • ψ y + t • ψ z) := by rw [hp]
    _ = (s • p + s • ψ y) + (t • p + t • ψ z) := by abel

/-! ## Transporting faces, vertices and edges along the chart -/

theorem chartMap_openSegment (p : EuclideanSpace ℝ (Fin d)) (y z : EuclideanSpace ℝ (Fin m)) :
    openSegment ℝ (chartMap ψ p y) (chartMap ψ p z) = chartMap ψ p '' openSegment ℝ y z := by
  ext w
  constructor
  · rintro ⟨s, t, hs, ht, hst, hw⟩
    exact ⟨s • y + t • z, ⟨s, t, hs, ht, hst, rfl⟩,
      by rw [chartMap_affine p s t hst, hw]⟩
  · rintro ⟨w', ⟨s, t, hs, ht, hst, hw'⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [← chartMap_affine p s t hst, hw']⟩

theorem chartMap_segment (p : EuclideanSpace ℝ (Fin d)) (y z : EuclideanSpace ℝ (Fin m)) :
    segment ℝ (chartMap ψ p y) (chartMap ψ p z) = chartMap ψ p '' segment ℝ y z := by
  ext w
  constructor
  · rintro ⟨s, t, hs, ht, hst, hw⟩
    exact ⟨s • y + t • z, ⟨s, t, hs, ht, hst, rfl⟩,
      by rw [chartMap_affine p s t hst, hw]⟩
  · rintro ⟨w', ⟨s, t, hs, ht, hst, hw'⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [← chartMap_affine p s t hst, hw']⟩

theorem chartMap_isExtreme (p : EuclideanSpace ℝ (Fin d))
    {S T : Set (EuclideanSpace ℝ (Fin m))} (h : IsExtreme ℝ S T) :
    IsExtreme ℝ (chartMap ψ p '' S) (chartMap ψ p '' T) := by
  constructor
  · exact Set.image_mono h.1
  · rintro x1 ⟨u1, hu1, rfl⟩ x2 ⟨u2, hu2, rfl⟩ x ⟨w, hw, rfl⟩ hseg
    rw [chartMap_openSegment] at hseg
    obtain ⟨w', hw', hww'⟩ := hseg
    have : w = w' := chartMap_injective p hww'.symm
    subst this
    exact ⟨u1, h.2 hu1 hu2 hw hw', rfl⟩

theorem chartMap_extremePoints (p : EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin m))) (y : EuclideanSpace ℝ (Fin m)) :
    y ∈ Set.extremePoints ℝ S ↔ chartMap ψ p y ∈ Set.extremePoints ℝ (chartMap ψ p '' S) := by
  constructor
  · intro hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro x1 ⟨u1, hu1, rfl⟩ x2 ⟨u2, hu2, rfl⟩ hseg
    rw [chartMap_openSegment] at hseg
    obtain ⟨w, hw, hww⟩ := hseg
    have : y = w := chartMap_injective p hww.symm
    subst this
    exact congrArg _ (hy.2 hu1 hu2 hw)
  · intro hy
    obtain ⟨⟨y', hy', hyy⟩, hmax⟩ := hy
    have hyy' : y' = y := chartMap_injective p hyy
    rw [hyy'] at hy'
    refine ⟨hy', ?_⟩
    intro u1 hu1 u2 hu2 hseg
    have h2 : chartMap ψ p y ∈ openSegment ℝ (chartMap ψ p u1) (chartMap ψ p u2) := by
      rw [chartMap_openSegment]
      exact ⟨y, hseg, rfl⟩
    have := hmax ⟨u1, hu1, rfl⟩ ⟨u2, hu2, rfl⟩ h2
    exact chartMap_injective p this

theorem chartMap_adj (p : EuclideanSpace ℝ (Fin d)) {S : Set (EuclideanSpace ℝ (Fin m))}
    {y z : EuclideanSpace ℝ (Fin m)} (h : Adj S y z) :
    Adj (chartMap ψ p '' S) (chartMap ψ p y) (chartMap ψ p z) := by
  refine ⟨fun hc => h.1 (chartMap_injective p hc), ?_⟩
  rw [chartMap_segment]
  exact chartMap_isExtreme p h.2

/-- A walk in the chart is a walk in the image. -/
theorem chartMap_reach (p : EuclideanSpace ℝ (Fin d)) {S : Set (EuclideanSpace ℝ (Fin m))}
    {L : ℕ} {y z : EuclideanSpace ℝ (Fin m)} (h : Reach S L y z) :
    Reach (chartMap ψ p '' S) L (chartMap ψ p y) (chartMap ψ p z) := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => chartMap ψ p (w i), by dsimp only; rw [h0], by dsimp only; rw [hL],
    fun i hi => ?_⟩
  dsimp only
  rcases hstep i hi with he | hadj
  · exact Or.inl (by rw [he])
  · exact Or.inr (chartMap_adj p hadj)

/-- A walk inside an extreme subset is a walk in the ambient set. -/
theorem reach_of_extreme {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q : Set E}
    (hQ : IsExtreme ℝ P Q) {L : ℕ} {u v : E} (h : Reach Q L u v) : Reach P L u v := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨w, h0, hL, fun i hi => ?_⟩
  rcases hstep i hi with he | hadj
  · exact Or.inl he
  · exact Or.inr ⟨hadj.1, IsExtreme.trans hQ hadj.2⟩

/-! ## The facet cut out by one tight inequality -/

variable (ψ)

/-- The face of `Hpoly a b` on which the `i`-th inequality is tight. -/
def facet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}

variable {ψ}

theorem facet_isExtreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (facet a b i) := by
  have h := HirschFace.exposed_isExtreme (Hpoly a b) (-(innerSL ℝ (a i)).toLinearMap) (-b i)
    (fun x hx => by
      have := hx i
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe, neg_le_neg_iff]
      exact this)
  have hset : {x | x ∈ Hpoly a b ∧ (-(innerSL ℝ (a i)).toLinearMap) x = -b i} = facet a b i := by
    ext x
    simp only [facet, Set.mem_setOf_eq, LinearMap.neg_apply, ContinuousLinearMap.coe_coe,
      neg_inj]
    rfl
  rwa [hset] at h

/-- The direction space of the hyperplane carrying the facet. -/
theorem finrank_perp (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = d - 1 := by
  have h1 : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = 1 :=
    finrank_span_singleton hv
  have hadd := Submodule.finrank_add_finrank_orthogonal
    (K := (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin d))))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  omega

theorem mem_perp_iff (v z : EuclideanSpace ℝ (Fin d)) :
    z ∈ (ℝ ∙ v)ᗮ ↔ ⟪v, z⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v)
  · intro h u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [real_inner_smul_left, h, mul_zero]

theorem facet_eq_image (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    (hrange : Set.range ψ = ((ℝ ∙ a i)ᗮ : Set (EuclideanSpace ℝ (Fin d))))
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ facet a b i) :
    chartMap ψ p '' (Hpoly (pullA ψ a) (pullB a b p)) = facet a b i := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(chartMap_mem_iff a b p y).mpr hy, ?_⟩
    have hmem : ψ y ∈ (ℝ ∙ a i)ᗮ := by
      rw [← SetLike.mem_coe, ← hrange]; exact ⟨y, rfl⟩
    have h0 : ⟪a i, ψ y⟫ = 0 := (mem_perp_iff _ _).mp hmem
    rw [chartMap, inner_add_right, h0, hp.2, add_zero]
  · intro hx
    have hxp : x - p ∈ (ℝ ∙ a i)ᗮ :=
      (mem_perp_iff _ _).mpr (by rw [inner_sub_right, hx.2, hp.2, sub_self])
    obtain ⟨y, hy⟩ : x - p ∈ Set.range ψ := by rw [hrange]; exact hxp
    have hxy : chartMap ψ p y = x := by rw [chartMap, hy]; abel
    refine ⟨y, ?_, hxy⟩
    rw [← chartMap_mem_iff a b p y, hxy]
    exact hx.1

theorem pullA_eq_zero (a : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hrange : Set.range ψ = ((ℝ ∙ a i)ᗮ : Set (EuclideanSpace ℝ (Fin d)))) :
    pullA ψ a i = 0 := by
  have hmem : ψ (pullA ψ a i) ∈ (ℝ ∙ a i)ᗮ := by
    rw [← SetLike.mem_coe, ← hrange]; exact ⟨_, rfl⟩
  have h0 : ⟪a i, ψ (pullA ψ a i)⟫ = 0 := (mem_perp_iff _ _).mp hmem
  have hself : ⟪pullA ψ a i, pullA ψ a i⟫ = 0 := by
    rw [pullA_inner a i (pullA ψ a i)]; exact h0
  rw [real_inner_self_eq_norm_sq] at hself
  have : ‖pullA ψ a i‖ = 0 := by nlinarith [norm_nonneg (pullA ψ a i)]
  exact norm_eq_zero.mp this

theorem pullB_eq_zero (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ facet a b i) : pullB a b p i = 0 := by
  simp [pullB, hp.2]

/-- An always-satisfied inequality may be deleted. -/
theorem hpoly_drop {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin m)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (ha : a i = 0) (hb : 0 ≤ b i) :
    Hpoly a b = Hpoly (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j)) := by
  ext y
  constructor
  · intro h j; exact h _
  · intro h j
    rcases eq_or_ne j i with rfl | hj
    · rw [ha]; simpa using hb
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'

set_option maxHeartbeats 1000000 in
/-- **The facet recursion.**  If every bounded polyhedron in `ℝ^(d-1)` cut out by `k`
inequalities has diameter at most `B`, then any two vertices of the facet of an
`(k+1)`-inequality polytope in `ℝ^d` are joined by a walk of `B` steps *in the polytope*. -/
theorem facet_reach {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hai : a i ≠ 0) (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (facet a b i))
    (hv : v ∈ Set.extremePoints ℝ (facet a b i)) :
    Reach (Hpoly a b) B u v := by
  classical
  set p : EuclideanSpace ℝ (Fin d) := u with hpdef
  have hp : p ∈ facet a b i := hu.1
  obtain ⟨ψ, hrange⟩ := exists_chart ((ℝ ∙ a i)ᗮ) (d - 1) (finrank_perp (a i) hai)
  set A : Fin k → EuclideanSpace ℝ (Fin (d - 1)) :=
    fun j => pullA ψ a (i.succAbove j) with hA
  set Bv : Fin k → ℝ := fun j => pullB a b p (i.succAbove j) with hBv
  have hdrop : Hpoly (pullA ψ a) (pullB a b p) = Hpoly A Bv :=
    hpoly_drop _ _ i (pullA_eq_zero a i hrange) (le_of_eq (pullB_eq_zero a b i hp).symm)
  have himg : chartMap ψ p '' (Hpoly A Bv) = facet a b i := by
    rw [← hdrop]; exact facet_eq_image a b i hrange hp
  -- the chart of a bounded facet is bounded
  have hbdF : Bornology.IsBounded (facet a b i) := hbd.subset (facet_isExtreme a b i).1
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdF
  have hbdA : Bornology.IsBounded (Hpoly A Bv) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖p‖, fun y hy => ?_⟩
    have h1 : chartMap ψ p y ∈ facet a b i := by rw [← himg]; exact ⟨y, hy, rfl⟩
    have h3 : ψ y = chartMap ψ p y - p := by rw [chartMap]; abel
    calc ‖y‖ = ‖ψ y‖ := (ψ.norm_map y).symm
      _ = ‖chartMap ψ p y - p‖ := by rw [h3]
      _ ≤ ‖chartMap ψ p y‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ C + ‖p‖ := by linarith [hC _ h1]
  -- pull the two vertices back to the chart
  have hpull : ∀ z ∈ Set.extremePoints ℝ (facet a b i),
      ∃ y ∈ Set.extremePoints ℝ (Hpoly A Bv), chartMap ψ p y = z := by
    intro z hz
    have hzi : z ∈ chartMap ψ p '' (Hpoly A Bv) := by rw [himg]; exact hz.1
    obtain ⟨y, hy, hyz⟩ := hzi
    refine ⟨y, ?_, hyz⟩
    refine (chartMap_extremePoints (ψ := ψ) p (Hpoly A Bv) y).mpr ?_
    rw [hyz, himg]
    exact hz
  obtain ⟨yu, hyu, hyu2⟩ := hpull u hu
  obtain ⟨yv, hyv, hyv2⟩ := hpull v hv
  have hreach : Reach (Hpoly A Bv) B yu yv := IH A Bv hbdA yu hyu yv hyv
  have h2 := chartMap_reach (ψ := ψ) p hreach
  rw [himg, hyu2, hyv2] at h2
  exact reach_of_extreme (facet_isExtreme a b i) h2

end HirschFacet

open HirschWalk HirschFacet

/-- **Facets are polyhedra of one dimension less.**  If every bounded H-polyhedron in
`ℝ^(d-1)` cut out by `k` inequalities has combinatorial diameter at most `B`, then any two
vertices of the face of a `(k+1)`-inequality polytope in `ℝ^d` on which the `i`-th
inequality is tight are joined by a walk of `B` steps in the polytope itself.  This is the
recursion step of the Barnette--Larman and Kalai--Kleitman inductions. -/
theorem solution (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) :=
  HirschFacet.facet_reach a b i hai hbd B IH hu hv
