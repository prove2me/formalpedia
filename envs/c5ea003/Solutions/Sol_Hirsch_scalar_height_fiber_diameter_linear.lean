-- Prove2me | solution 1 for Hirsch.scalar_height_fiber_diameter_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T06:25:35.850124+00:00
-- url     : https://prove2.me/submissions/14732ae7-8dd3-45a9-8bcf-e6df374ef38b

import Mathlib
import Definitions.Def_Hirsch_scalar_fiber_model

set_option autoImplicit false

open scoped RealInnerProductSpace BigOperators

namespace P2Mb372

open Hirsch

/-! ## Walk algebra on `EndpointWalkLE` -/

section walks
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem adj_symm {Q : Set E} {a b : E} (h : Adj Q a b) : Adj Q b a := by
  refine ⟨h.1.symm, ?_⟩
  rw [segment_symm]; exact h.2

theorem walk_refl (Q : Set E) (B : ℕ) (x : E) : EndpointWalkLE Q B x x :=
  ⟨fun _ => x, rfl, rfl, fun _ _ => Or.inl rfl⟩

theorem walk_single {Q : Set E} {x y : E} (h : Adj Q x y) : EndpointWalkLE Q 1 x y := by
  refine ⟨fun j => if j = 0 then x else y, by simp, by simp, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  right
  simpa using h

theorem walk_mono {Q : Set E} {B B' : ℕ} {x y : E} (hB : B ≤ B')
    (h : EndpointWalkLE Q B x y) : EndpointWalkLE Q B' x y := by
  obtain ⟨w, h0, hB1, hs⟩ := h
  refine ⟨fun j => w (min j B), by simpa using h0, by simpa [min_eq_right hB] using hB1, ?_⟩
  intro j hj
  by_cases hjB : j < B
  · have e1 : min j B = j := min_eq_left hjB.le
    have e2 : min (j+1) B = j + 1 := min_eq_left hjB
    simp only [e1, e2]; exact hs j hjB
  · left
    have e1 : min j B = B := min_eq_right (by omega)
    have e2 : min (j+1) B = B := min_eq_right (by omega)
    simp only [e1, e2]

theorem walk_trans {Q : Set E} {B₁ B₂ : ℕ} {x y z : E} (h₁ : EndpointWalkLE Q B₁ x y)
    (h₂ : EndpointWalkLE Q B₂ y z) : EndpointWalkLE Q (B₁ + B₂) x z := by
  obtain ⟨w₁, a0, a1, as⟩ := h₁
  obtain ⟨w₂, b0, b1, bs⟩ := h₂
  refine ⟨fun j => if j ≤ B₁ then w₁ j else w₂ (j - B₁), by simp [a0], ?_, ?_⟩
  · by_cases hB : B₂ = 0
    · subst hB
      simp only [add_zero, le_refl, if_true, a1]
      rw [← b0]; exact b1
    · have : ¬ (B₁ + B₂ ≤ B₁) := by omega
      simp only [this, if_false]
      rw [show B₁ + B₂ - B₁ = B₂ by omega]; exact b1
  · intro j hj
    by_cases hj1 : j + 1 ≤ B₁
    · have hj0 : j ≤ B₁ := by omega
      simp only [hj0, hj1, if_true]; exact as j (by omega)
    · by_cases hj0 : j ≤ B₁
      · have hjB : j = B₁ := by omega
        subst hjB
        simp only [le_refl, if_true, hj1, if_false]
        rw [show j + 1 - j = 0 + 1 by omega, a1, ← b0]; exact bs 0 (by omega)
      · simp only [hj0, hj1, if_false]
        rw [show j + 1 - B₁ = (j - B₁) + 1 by omega]; exact bs (j - B₁) (by omega)

theorem walk_symm {Q : Set E} {B : ℕ} {x y : E} (h : EndpointWalkLE Q B x y) :
    EndpointWalkLE Q B y x := by
  obtain ⟨w, h0, h1, hs⟩ := h
  refine ⟨fun j => w (B - j), by simpa using h1, by simpa using h0, ?_⟩
  intro j hj
  have e : B - j = (B - (j+1)) + 1 := by omega
  simp only
  rw [e]
  rcases hs (B - (j+1)) (by omega) with h | h
  · left; exact h.symm
  · right; exact adj_symm h

theorem walk_map {E' : Type*} [AddCommGroup E'] [Module ℝ E'] {Q : Set E} {Q' : Set E'}
    (f : E → E') (hf : ∀ a b, Adj Q a b → Adj Q' (f a) (f b)) {B : ℕ} {x y : E}
    (h : EndpointWalkLE Q B x y) : EndpointWalkLE Q' B (f x) (f y) := by
  obtain ⟨w, h0, h1, hs⟩ := h
  refine ⟨fun j => f (w j), by simp [h0], by simp [h1], fun j hj => ?_⟩
  rcases hs j hj with h | h
  · left; simp [h]
  · right; exact hf _ _ h

theorem adj_of_face {Q Q' : Set E} (hQ : IsExtreme ℝ Q Q') {a b : E} (h : Adj Q' a b) :
    Adj Q a b := ⟨h.1, hQ.trans h.2⟩

theorem walk_of_face {Q Q' : Set E} (hQ : IsExtreme ℝ Q Q') {B : ℕ} {x y : E}
    (h : EndpointWalkLE Q' B x y) : EndpointWalkLE Q B x y :=
  walk_map id (fun _ _ hab => adj_of_face hQ hab) h

end walks

/-! ## Second-best vertex is adjacent (port of kb/lemmas/hpoly_faces.lean `main`) -/

section sb
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem shrink (φ : E →L[ℝ] ℝ) (x₁ x₂ z : E) (β : ℝ) (hz : β < φ z)
    (hzs : z ∈ openSegment ℝ x₁ x₂) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ β ≤ φ (z + δ • (x₁ - z)) ∧ β ≤ φ (z + δ • (x₂ - z)) ∧
      z ∈ openSegment ℝ (z + δ • (x₁ - z)) (z + δ • (x₂ - z)) := by
  set e := φ z - β with he
  have he0 : 0 < e := by rw [he]; linarith
  set D := |φ x₁ - φ z| + |φ x₂ - φ z| with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨e / (e + D), by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · have hδD : e / (e + D) * D ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    have h1 : -|φ x₁ - φ z| ≤ φ x₁ - φ z := neg_abs_le _
    have h2 : 0 ≤ e / (e + D) := by positivity
    have h3 : |φ x₁ - φ z| ≤ D := by rw [hD]; have := abs_nonneg (φ x₂ - φ z); linarith
    nlinarith
  · have hδD : e / (e + D) * D ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    have h1 : -|φ x₂ - φ z| ≤ φ x₂ - φ z := neg_abs_le _
    have h2 : 0 ≤ e / (e + D) := by positivity
    have h3 : |φ x₂ - φ z| ≤ D := by rw [hD]; have := abs_nonneg (φ x₁ - φ z); linarith
    nlinarith
  · obtain ⟨s, t, hs, ht, hst, hzeq⟩ := hzs
    refine ⟨s, t, hs, ht, hst, ?_⟩
    obtain rfl : t = 1 - s := by linarith
    have hz' : z = s • x₁ + (1 - s) • x₂ := hzeq.symm
    set δ := e / (e + D)
    calc s • (z + δ • (x₁ - z)) + (1 - s) • (z + δ • (x₂ - z))
        = z + δ • ((s • x₁ + (1 - s) • x₂) - z) := by module
      _ = z := by rw [← hz', sub_self, smul_zero, add_zero]

theorem max_ext (P : Set E) (φ : E →L[ℝ] ℝ) (v : E) (hc : ∀ x ∈ P, x ≠ v → φ x < φ v) :
    ∀ x₁ ∈ P, ∀ x₂ ∈ P, v ∈ openSegment ℝ x₁ x₂ → x₁ = v := by
  intro x₁ hx₁ x₂ hx₂ hseg
  by_contra hne
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hseg
  have h1 := hc x₁ hx₁ hne
  have h2 : φ x₂ ≤ φ v := by
    by_cases h : x₂ = v
    · rw [h]
    · exact (hc x₂ hx₂ h).le
  have h3 : φ v = s * φ x₁ + t * φ x₂ := by
    rw [← heq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_pos hs (sub_pos.2 h1), mul_nonneg ht.le (sub_nonneg.2 h2)]

theorem line_seg (P : Set E) (φ : E →L[ℝ] ℝ) (u v : E) (hc : ∀ x ∈ P, x ≠ v → φ x < φ v)
    (hv : v ∈ P) (hu : u ∈ P.extremePoints ℝ) (huv : u ≠ v) (x : E) (hx : x ∈ P) (τ : ℝ)
    (hxe : x = v + τ • (u - v)) : x ∈ segment ℝ v u := by
  have hlt : φ u < φ v := hc u hu.1 huv
  have hφx : φ x = φ v + τ * (φ u - φ v) := by
    rw [hxe, map_add, map_smul, map_sub, smul_eq_mul]
  have hxle : φ x ≤ φ v := by
    by_cases h : x = v
    · rw [h]
    · exact (hc x hx h).le
  have hτ0 : 0 ≤ τ := by
    by_contra h
    push Not at h
    nlinarith
  have hτ1 : τ ≤ 1 := by
    by_contra h
    push Not at h
    have hτpos : 0 < τ := by linarith
    have hseg : u ∈ openSegment ℝ v x := by
      refine ⟨1 - 1 / τ, 1 / τ, ?_, by positivity, by ring, ?_⟩
      · rw [sub_pos, div_lt_one hτpos]; exact h
      · rw [hxe]
        have hτne : τ ≠ 0 := hτpos.ne'
        match_scalars <;> (field_simp; try ring)
    exact huv ((hu.2 hv hx hseg).symm)
  refine ⟨1 - τ, τ, by linarith, hτ0, by ring, ?_⟩
  rw [hxe]; module

theorem sb (P : Set E) (hPc : IsCompact P) (hPconv : Convex ℝ P) (φ : E →L[ℝ] ℝ)
    (v : E) (hv : v ∈ P) (hc : ∀ x ∈ P, x ≠ v → φ x < φ v)
    (u : E) (hu : u ∈ P.extremePoints ℝ) (huv : u ≠ v)
    (hbest : ∀ u' ∈ P.extremePoints ℝ, u' ≠ v → φ u' ≤ φ u) :
    Adj P v u := by
  have hPclosed : IsClosed P := hPc.isClosed
  have hcomb : ∀ z ∈ P, ∀ x ∈ P, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → z + δ • (x - z) ∈ P := by
    intro z hz x hx δ h0 h1
    have := hPconv hz hx (sub_nonneg.2 h1) h0 (by ring)
    convert this using 1
    module
  have huP : u ∈ P := hu.1
  have hlt : φ u < φ v := hc u huP huv
  set β := φ u with hβ
  set K := P ∩ {x | β ≤ φ x} with hK
  set B := P ∩ {x | φ x = β} with hB
  have hHconv : Convex ℝ {x : E | β ≤ φ x} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    obtain rfl : t = 1 - s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  have hHBconv : Convex ℝ {x : E | φ x = β} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy]
    rw [← add_mul, hst, one_mul]
  have hKconv : Convex ℝ K := hPconv.inter hHconv
  have hBconv : Convex ℝ B := hPconv.inter hHBconv
  have hKclosed : IsClosed K :=
    hPclosed.inter (isClosed_le continuous_const φ.continuous)
  have hBclosed : IsClosed B :=
    hPclosed.inter (isClosed_eq φ.continuous continuous_const)
  have hKcomp : IsCompact K := hPc.of_isClosed_subset hKclosed Set.inter_subset_left
  have hBcomp : IsCompact B := hPc.of_isClosed_subset hBclosed Set.inter_subset_left
  -- extreme points of K lie in {v} ∪ B
  have hextK : K.extremePoints ℝ ⊆ insert v B := by
    intro e he
    have heK : e ∈ K := he.1
    rcases eq_or_lt_of_le (show β ≤ φ e from heK.2) with h | h
    · right; exact ⟨heK.1, h.symm⟩
    · left
      by_contra hev
      have heP : e ∈ P.extremePoints ℝ := by
        refine ⟨heK.1, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩
        obtain ⟨δ, hδ0, hδ1, h1, h2, hseg'⟩ := shrink φ x₁ x₂ e β h hseg
        have hx₁' : e + δ • (x₁ - e) ∈ K := ⟨hcomb e heK.1 x₁ hx₁ δ hδ0.le hδ1, h1⟩
        have hx₂' : e + δ • (x₂ - e) ∈ K := ⟨hcomb e heK.1 x₂ hx₂ δ hδ0.le hδ1, h2⟩
        have heq := he.2 hx₁' hx₂' hseg'
        have h0 : δ • (x₁ - e) = 0 := by
          have := congrArg (fun w => w - e) heq
          simpa using this
        rcases smul_eq_zero.1 h0 with h' | h'
        · exact absurd h' hδ0.ne'
        · exact sub_eq_zero.1 h'
      exact absurd (hbest e heP hev) (not_le.2 h)
  -- the pyramid S
  set S := (fun p : ℝ × E => (1 - p.1) • v + p.1 • p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ B) with hS
  have hScomp : IsCompact S := (isCompact_Icc.prod hBcomp).image (by fun_prop)
  have hBne : B.Nonempty := ⟨u, huP, rfl⟩
  have hhullS : convexHull ℝ (insert v B) ⊆ S := by
    rw [convexHull_insert hBne, hBconv.convexHull_eq, convexJoin_singleton_left]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, p, q, hp, hq, hpq, rfl⟩ := hx
    refine ⟨(q, y), ⟨⟨hq, by linarith⟩, hy⟩, ?_⟩
    simp only
    rw [show p = 1 - q by linarith]
  have hKS : K ⊆ S := by
    have hKM := closure_convexHull_extremePoints hKcomp hKconv
    intro x hx
    rw [← hKM] at hx
    exact closure_minimal ((convexHull_mono hextK).trans hhullS) hScomp.isClosed hx
  have hvext := max_ext P φ v hc
  have hline := line_seg P φ u v hc hv hu huv
  have key : ∀ x₁ ∈ P, ∀ x₂ ∈ P, ∀ z ∈ segment ℝ v u, z ∈ openSegment ℝ x₁ x₂ →
      x₁ ∈ segment ℝ v u := by
    intro x₁ hx₁ x₂ hx₂ z hz hzo
    obtain ⟨p, q, hp, hq, hpq, hzeq⟩ := hz
    obtain rfl : p = 1 - q := by linarith
    rcases eq_or_lt_of_le hq with hq0 | hq0
    · have hzv : z = v := by rw [← hzeq, ← hq0]; simp
      subst hzv
      rw [hvext x₁ hx₁ x₂ hx₂ hzo]; exact left_mem_segment ℝ z u
    rcases eq_or_lt_of_le hp with hq1 | hq1
    · have hq1' : q = 1 := by linarith
      have hzu : z = u := by rw [← hzeq, hq1']; simp
      subst hzu
      rw [hu.2 hx₁ hx₂ hzo]; exact right_mem_segment ℝ v z
    have hφz : φ z = (1 - q) * φ v + q * β := by
      rw [← hzeq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hzβ : β < φ z := by
      rw [hφz]; nlinarith
    have hzP : z ∈ P := by
      have := hcomb v hv u huP q hq (by linarith)
      convert this using 1
      rw [← hzeq]; module
    obtain ⟨δ, hδ0, hδ1, h1, h2, hseg'⟩ := shrink φ x₁ x₂ z β hzβ hzo
    have hx₁K : z + δ • (x₁ - z) ∈ K := ⟨hcomb z hzP x₁ hx₁ δ hδ0.le hδ1, h1⟩
    have hx₂K : z + δ • (x₂ - z) ∈ K := ⟨hcomb z hzP x₂ hx₂ δ hδ0.le hδ1, h2⟩
    obtain ⟨⟨l₁, y₁⟩, ⟨⟨hl₁0, hl₁1⟩, hy₁B⟩, hy₁eq⟩ := hKS hx₁K
    obtain ⟨⟨l₂, y₂⟩, ⟨⟨hl₂0, hl₂1⟩, hy₂B⟩, hy₂eq⟩ := hKS hx₂K
    simp only at hy₁eq hy₂eq hl₁0 hl₁1 hl₂0 hl₂1 hy₁B hy₂B
    obtain ⟨s, t, hs, ht, hst, hstz⟩ := hseg'
    have hφ1 : φ (z + δ • (x₁ - z)) = (1 - l₁) * φ v + l₁ * β := by
      rw [← hy₁eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hy₁B.2]
    have hφ2 : φ (z + δ • (x₂ - z)) = (1 - l₂) * φ v + l₂ * β := by
      rw [← hy₂eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hy₂B.2]
    have hφs : φ z = s * φ (z + δ • (x₁ - z)) + t * φ (z + δ • (x₂ - z)) := by
      conv_lhs => rw [← hstz]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hqeq : q = s * l₁ + t * l₂ := by
      rw [hφz, hφ1, hφ2] at hφs
      have h0 : (φ v - β) * (q - (s * l₁ + t * l₂)) = 0 := by
        linear_combination -hφs - φ v * hst
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (sub_ne_zero.2 hlt.ne')
      · linarith
    have hvec0 : (1 - q) • v + q • u =
        s • ((1 - l₁) • v + l₁ • y₁) + t • ((1 - l₂) • v + l₂ • y₂) := by
      calc (1 - q) • v + q • u = z := hzeq
        _ = s • (z + δ • (x₁ - z)) + t • (z + δ • (x₂ - z)) := hstz.symm
        _ = _ := by rw [hy₁eq, hy₂eq]
    have hvec : q • u = (s * l₁) • y₁ + (t * l₂) • y₂ := by
      obtain rfl : t = 1 - s := by linarith
      rw [hqeq] at hvec0 ⊢
      linear_combination (norm := module) hvec0
    have hy₁u : l₁ = 0 ∨ y₁ = u := by
      rcases eq_or_lt_of_le hl₁0 with h | hl₁pos
      · left; exact h.symm
      right
      rcases eq_or_lt_of_le hl₂0 with h' | hl₂pos
      · rw [← h', mul_zero, zero_smul, add_zero] at hvec
        rw [← h', mul_zero, add_zero] at hqeq
        rw [← hqeq] at hvec
        exact (smul_right_injective _ hq0.ne' hvec).symm
      · have hseg : u ∈ openSegment ℝ y₁ y₂ := by
          refine ⟨s * l₁ / q, t * l₂ / q, by positivity, by positivity, ?_, ?_⟩
          · rw [← add_div, ← hqeq, div_self hq0.ne']
          · calc (s * l₁ / q) • y₁ + (t * l₂ / q) • y₂
                = q⁻¹ • ((s * l₁) • y₁ + (t * l₂) • y₂) := by
                  rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
              _ = u := by rw [← hvec, smul_smul, inv_mul_cancel₀ hq0.ne', one_smul]
        exact hu.2 hy₁B.1 hy₂B.1 hseg
    have hx₁'eq : z + δ • (x₁ - z) = (1 - l₁) • v + l₁ • u := by
      rw [← hy₁eq]
      rcases hy₁u with h | h
      · rw [h]; simp
      · rw [h]
    apply hline x₁ hx₁ (q + δ⁻¹ * (l₁ - q))
    have hδx : δ • (x₁ - z) = (1 - l₁) • v + l₁ • u - z := by rw [← hx₁'eq]; abel
    have hx : x₁ - z = δ⁻¹ • ((1 - l₁) • v + l₁ • u - z) := by
      rw [← hδx, inv_smul_smul₀ hδ0.ne']
    have hx' : x₁ = z + δ⁻¹ • ((1 - l₁) • v + l₁ • u - z) := by rw [← hx]; abel
    rw [hx', ← hzeq]
    module
  refine ⟨huv.symm, ⟨?_, ?_⟩⟩
  · intro x hx
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
    have := hcomb v hv u huP q hq (by linarith)
    convert this using 1
    rw [show p = 1 - q by linarith]; module
  · intro x₁ hx₁ x₂ hx₂ z hz hzo
    exact key x₁ hx₁ x₂ hx₂ z hz hzo

end sb

/-! ## Generic polytope toolkit: Krein–Milman hull, exposing functional, improving neighbour -/

section toolkit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conv_ext {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q)
    (hfin : (Q.extremePoints ℝ).Finite) : convexHull ℝ (Q.extremePoints ℝ) = Q := by
  have h := closure_convexHull_extremePoints hQc hQv
  rwa [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq] at h

theorem convex_lt (ψ : E →L[ℝ] ℝ) (c : ℝ) : Convex ℝ {z : E | ψ z < c} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have : t = 1 := by linarith
    subst this; simpa using hb
  · have h1 := mul_lt_mul_of_pos_left ha h
    have h2 := mul_le_mul_of_nonneg_left hb.le ht
    have h3 : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    linarith

theorem convex_le (ψ : E →L[ℝ] ℝ) (c : ℝ) : Convex ℝ {z : E | ψ z ≤ c} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left ha hs
  have h2 := mul_le_mul_of_nonneg_left hb ht
  have h3 : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
  linarith

theorem strict_of_vertices {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q)
    (hfin : (Q.extremePoints ℝ).Finite) (ψ : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ Q.extremePoints ℝ)
    (hψ : ∀ y ∈ Q.extremePoints ℝ, y ≠ x → ψ y < ψ x) : ∀ y ∈ Q, y ≠ x → ψ y < ψ x := by
  intro y hy hyx
  have hVeq : Q.extremePoints ℝ = insert x (Q.extremePoints ℝ \ {x}) := by
    rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hx]
  rw [← conv_ext hQc hQv hfin] at hy
  by_cases hW : (Q.extremePoints ℝ \ {x}).Nonempty
  · rw [hVeq, convexHull_insert hW, convexJoin_singleton_left] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨w, hw, p, q, hp, hq, hpq, rfl⟩ := hy
    have hwlt : ψ w < ψ x :=
      convexHull_min (fun z hz => hψ z hz.1 hz.2) (convex_lt ψ (ψ x)) hw
    have hq0 : 0 < q := by
      rcases eq_or_lt_of_le hq with h | h
      · exfalso; apply hyx
        rw [← h, zero_smul, add_zero, show p = 1 by linarith, one_smul]
      · exact h
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    obtain rfl : p = 1 - q := by linarith
    nlinarith
  · have hW' : Q.extremePoints ℝ \ {x} = ∅ := Set.not_nonempty_iff_eq_empty.1 hW
    rw [hVeq, hW', insert_empty_eq, convexHull_singleton] at hy
    exact absurd hy hyx

theorem exposed {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q)
    (hfin : (Q.extremePoints ℝ).Finite) {x : E} (hx : x ∈ Q.extremePoints ℝ) :
    ∃ g : E →L[ℝ] ℝ, ∀ y ∈ Q, y ≠ x → g y < g x := by
  have hWfin : (Q.extremePoints ℝ \ {x}).Finite := hfin.subset Set.diff_subset
  have hC : IsClosed (convexHull ℝ (Q.extremePoints ℝ \ {x})) :=
    (hWfin.isCompact_convexHull ℝ).isClosed
  have hxC : x ∉ convexHull ℝ (Q.extremePoints ℝ \ {x}) := by
    intro hmem
    have hsub : convexHull ℝ (Q.extremePoints ℝ \ {x}) ⊆ Q :=
      convexHull_min (fun z hz => hz.1.1) hQv
    have h1 : x ∈ (convexHull ℝ (Q.extremePoints ℝ \ {x})).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hmem, hx⟩
    have h2 := extremePoints_convexHull_subset h1
    exact h2.2 (Set.mem_singleton x)
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hC hxC
  refine ⟨-f, strict_of_vertices hQc hQv hfin (-f) hx ?_⟩
  intro y hy hyx
  have := hfb y (subset_convexHull ℝ _ ⟨hy, hyx⟩)
  simp only [ContinuousLinearMap.neg_apply]
  linarith

theorem improve {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q)
    (hfin : (Q.extremePoints ℝ).Finite) (φ : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ Q.extremePoints ℝ) (hnot : ∃ y ∈ Q, φ x < φ y) :
    ∃ x' ∈ Q.extremePoints ℝ, Adj Q x x' ∧ φ x < φ x' := by
  classical
  obtain ⟨g, hg⟩ := exposed hQc hQv hfin hx
  have hVp : ∃ y ∈ Q.extremePoints ℝ, φ x < φ y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hlt⟩ := hnot
    have hy' : y ∈ convexHull ℝ (Q.extremePoints ℝ) := by
      rw [conv_ext hQc hQv hfin]; exact hy
    have : y ∈ {z : E | φ z ≤ φ x} :=
      convexHull_min (fun z hz => hcon z hz) (convex_le φ (φ x)) hy'
    exact absurd this (not_le.2 hlt)
  set V := hfin.toFinset with hV
  have memV : ∀ y, y ∈ V ↔ y ∈ Q.extremePoints ℝ := fun y => Set.Finite.mem_toFinset hfin
  set Vp := V.filter (fun y => φ x < φ y) with hVpdef
  have hVpne : Vp.Nonempty := by
    obtain ⟨y, hy, hlt⟩ := hVp
    exact ⟨y, Finset.mem_filter.2 ⟨(memV y).2 hy, hlt⟩⟩
  obtain ⟨ys, hys, hmin⟩ := Vp.exists_min_image (fun y => (g x - g y) / (φ y - φ x)) hVpne
  have hysV := (Finset.mem_filter.1 hys)
  have hysE : ys ∈ Q.extremePoints ℝ := (memV ys).1 hysV.1
  have hysx : ys ≠ x := by
    intro h; rw [h] at hysV; exact lt_irrefl _ hysV.2
  have hdpos : 0 < φ ys - φ x := sub_pos.2 hysV.2
  set μs := (g x - g ys) / (φ ys - φ x) with hμs
  have hgys : g ys < g x := hg ys hysE.1 hysx
  have hμspos : 0 < μs := div_pos (sub_pos.2 hgys) hdpos
  have hμsmul : μs * (φ ys - φ x) = g x - g ys := by
    rw [hμs, div_mul_cancel₀ _ hdpos.ne']
  set W := V.filter (fun y => y ≠ x) with hWdef
  have hysW : ys ∈ W := Finset.mem_filter.2 ⟨hysV.1, hysx⟩
  have hWne : W.Nonempty := ⟨ys, hysW⟩
  obtain ⟨ym, hym, hmin2⟩ := W.exists_min_image (fun y => g x - g y) hWne
  have hymW := Finset.mem_filter.1 hym
  set δ := g x - g ym with hδdef
  have hδ : 0 < δ := sub_pos.2 (hg ym ((memV ym).1 hymW.1).1 hymW.2)
  set ε := δ / (2 * (φ ys - φ x)) with hεdef
  have hεpos : 0 < ε := div_pos hδ (by linarith)
  have hεmul : ε * (φ ys - φ x) = δ / 2 := by
    rw [hεdef]; field_simp
  set μ := max 0 (μs - ε) with hμdef
  have hμ0 : 0 ≤ μ := le_max_left _ _
  have hμlt : μ < μs := max_lt hμspos (by linarith)
  have hμge : μs - ε ≤ μ := le_max_right _ _
  set ψ : E →L[ℝ] ℝ := g + μ • φ with hψdef
  have hψapp : ∀ y, ψ y = g y + μ * φ y := by
    intro y; simp [hψdef]
  have hψV : ∀ y ∈ Q.extremePoints ℝ, y ≠ x → ψ y < ψ x := by
    intro y hy hyx
    rw [hψapp, hψapp]
    rcases lt_or_ge (φ x) (φ y) with hlt | hle
    · have hyVp : y ∈ Vp := Finset.mem_filter.2 ⟨(memV y).2 hy, hlt⟩
      have hr := hmin y hyVp
      simp only at hr
      have hd : 0 < φ y - φ x := sub_pos.2 hlt
      have h1 : μs * (φ y - φ x) ≤ g x - g y := by
        rw [← le_div_iff₀ hd]; exact hr
      have h2 : μ * (φ y - φ x) < μs * (φ y - φ x) := mul_lt_mul_of_pos_right hμlt hd
      linarith
    · have hgy : g y < g x := hg y hy.1 hyx
      have : μ * φ y ≤ μ * φ x := mul_le_mul_of_nonneg_left hle hμ0
      linarith
  obtain ⟨u, hu, hmax⟩ := W.exists_max_image ψ hWne
  have huW := Finset.mem_filter.1 hu
  have huE : u ∈ Q.extremePoints ℝ := (memV u).1 huW.1
  have hφu : φ x < φ u := by
    by_contra hcon
    push Not at hcon
    have h1 := hmin2 u hu
    simp only at h1
    have h2 := hmax ys hysW
    rw [hψapp, hψapp] at h2
    have h3 : μ * φ u ≤ μ * φ x := mul_le_mul_of_nonneg_left hcon hμ0
    have h4 : (μs - μ) * (φ ys - φ x) ≤ ε * (φ ys - φ x) :=
      mul_le_mul_of_nonneg_right (by linarith) hdpos.le
    nlinarith
  refine ⟨u, huE, ?_, hφu⟩
  have hψQ := strict_of_vertices hQc hQv hfin ψ hx hψV
  refine sb Q hQc hQv ψ x hx.1 hψQ u huE huW.2 ?_
  intro u' hu' hne
  exact hmax u' (Finset.mem_filter.2 ⟨(memV u').2 hu', hne⟩)

theorem path {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q)
    (hfin : (Q.extremePoints ℝ).Finite) (φ : E →L[ℝ] ℝ) (Φ : Finset ℝ)
    (hΦ : ∀ y ∈ Q.extremePoints ℝ, φ y ∈ Φ) :
    ∀ n : ℕ, ∀ x ∈ Q.extremePoints ℝ, (Φ.filter (fun t => φ x < t)).card ≤ n →
      ∃ x' ∈ Q.extremePoints ℝ, (∀ y ∈ Q, φ y ≤ φ x') ∧ EndpointWalkLE Q n x x' := by
  intro n
  induction n with
  | zero =>
    intro x hx hcard
    refine ⟨x, hx, ?_, walk_refl Q 0 x⟩
    intro y hy
    by_contra hlt
    push Not at hlt
    obtain ⟨x', hx', _, hlt'⟩ := improve hQc hQv hfin φ hx ⟨y, hy, hlt⟩
    have hm : φ x' ∈ Φ.filter (fun t => φ x < t) := Finset.mem_filter.2 ⟨hΦ x' hx', hlt'⟩
    have := Finset.card_pos.2 ⟨_, hm⟩
    omega
  | succ n ih =>
    intro x hx hcard
    by_cases hmax : ∀ y ∈ Q, φ y ≤ φ x
    · exact ⟨x, hx, hmax, walk_refl Q _ x⟩
    · push Not at hmax
      obtain ⟨x', hx', hadj, hlt⟩ := improve hQc hQv hfin φ hx hmax
      have hsub : Φ.filter (fun t => φ x' < t) ⊂ Φ.filter (fun t => φ x < t) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨φ x', Finset.mem_filter.2 ⟨hΦ x' hx', hlt⟩, ?_⟩
          simp
        · intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          exact ⟨ht.1, hlt.trans ht.2⟩
      have hlt2 := Finset.card_lt_card hsub
      obtain ⟨x'', hx'', hmax'', hwalk⟩ := ih x' hx' (by omega)
      exact ⟨x'', hx'', hmax'', walk_mono (by omega) (walk_trans (walk_single hadj) hwalk)⟩

end toolkit

/-! ## Slices of a polytope by a level set of an affine height -/

section slices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem aff_add (h : E →ᵃ[ℝ] ℝ) (x y : E) : h (x + y) = h x + h.linear y := by
  have := h.map_vadd x y
  rw [vadd_eq_add, vadd_eq_add] at this
  rw [add_comm x y, this, add_comm]

theorem line_mem {P : Set E} (hPv : Convex ℝ P) {x y : E} (hp : x + y ∈ P) (hm : x - y ∈ P)
    (μ : ℝ) (h1 : -1 ≤ μ) (h2 : μ ≤ 1) : x + μ • y ∈ P := by
  have := hPv hp hm (show (0:ℝ) ≤ (1 + μ) / 2 by linarith)
    (show (0:ℝ) ≤ (1 - μ) / 2 by linarith) (by ring)
  convert this using 1
  module

theorem two_sided {P : Set E} (hPv : Convex ℝ P) {x : E} (hx : x ∈ P)
    (hne : x ∉ P.extremePoints ℝ) : ∃ y : E, y ≠ 0 ∧ x + y ∈ P ∧ x - y ∈ P := by
  have hnot : ¬ (∀ x₁ ∈ P, ∀ x₂ ∈ P, x ∈ openSegment ℝ x₁ x₂ → x₁ = x) :=
    fun h => hne ⟨hx, fun x₁ hx₁ x₂ hx₂ hs => h x₁ hx₁ x₂ hx₂ hs⟩
  push Not at hnot
  obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne1⟩ := hnot
  obtain ⟨s, t, hs, ht, hst, hxeq⟩ := hseg
  obtain rfl : t = 1 - s := by linarith
  have h12 : x₁ ≠ x₂ := by
    intro h; apply hne1; rw [← hxeq, h]; module
  refine ⟨(s * (1 - s)) • (x₁ - x₂), ?_, ?_, ?_⟩
  · intro h0
    rcases smul_eq_zero.1 h0 with h | h
    · have : 0 < s * (1 - s) := mul_pos hs ht
      linarith
    · exact h12 (sub_eq_zero.1 h)
  · have := hPv hx hx₁ (show (0:ℝ) ≤ 1 - s by linarith) hs.le (by ring)
    convert this using 1
    rw [← hxeq]; module
  · have := hPv hx hx₂ (show (0:ℝ) ≤ 1 - (1 - s) by linarith) ht.le (by ring)
    convert this using 1
    rw [← hxeq]; module

theorem slack {P : Set E} (hPv : Convex ℝ P) {x y0 : E}
    (hline : ∀ μ : ℝ, -1 ≤ μ → μ ≤ 1 → x + μ • y0 ∈ P) {p u : E} {β : ℝ} (hp : p ∈ P)
    (hpu : p = x + u + β • y0) : ∃ ε : ℝ, 0 < ε ∧ x + ε • u ∈ P := by
  have hb : 0 < β ^ 2 + 1 := by positivity
  have hb2 : 0 < β ^ 2 + 2 := by positivity
  set ε := 1 / (β ^ 2 + 2) with hε
  set μ := -β / (β ^ 2 + 1) with hμ
  have hε0 : 0 < ε := by positivity
  have hε1 : 0 ≤ 1 - ε := by
    rw [hε, sub_nonneg, div_le_one hb2]; nlinarith
  have hμ1 : -1 ≤ μ := by
    rw [hμ, le_div_iff₀ hb]; nlinarith [sq_nonneg (β - 1), sq_nonneg β]
  have hμ2 : μ ≤ 1 := by
    rw [hμ, div_le_iff₀ hb]; nlinarith [sq_nonneg (β + 1), sq_nonneg β]
  have hkey : (1 - ε) * μ = -(ε * β) := by
    rw [hε, hμ]; field_simp; ring
  refine ⟨ε, hε0, ?_⟩
  have hmem := hPv hp (hline μ hμ1 hμ2) hε0.le hε1 (by ring)
  have e1 : (1 - ε) • (x + μ • y0) = (1 - ε) • x + (-(ε * β)) • y0 := by
    rw [← hkey]; module
  convert hmem using 1
  rw [e1, hpu]; module

theorem slice_edge {P : Set E} (hPc : IsCompact P) (hPv : Convex ℝ P)
    (L : E →ₗ[ℝ] ℝ) {x : E} (hx : x ∈ P)
    (hS : ∀ y : E, x + y ∈ P → ∀ c : ℝ, 0 < c → x - c • y ∈ P → L y = 0 → y = 0)
    (hne : x ∉ P.extremePoints ℝ) :
    ∃ a b : E, Adj P a b ∧ x ∈ segment ℝ a b ∧ L a ≠ L b := by
  obtain ⟨y0, hy0, hp, hm⟩ := two_sided hPv hx hne
  have hLy0 : L y0 ≠ 0 := by
    intro h0; exact hy0 (hS y0 hp 1 one_pos (by simpa using hm) h0)
  have hline : ∀ μ : ℝ, -1 ≤ μ → μ ≤ 1 → x + μ • y0 ∈ P := line_mem hPv hp hm
  set T : Set ℝ := {l | x + l • y0 ∈ P} with hT
  have hTclosed : IsClosed T :=
    hPc.isClosed.preimage (by fun_prop : Continuous fun l : ℝ => x + l • y0)
  obtain ⟨R, hR⟩ := hPc.isBounded.exists_norm_le
  have hy0n : 0 < ‖y0‖ := norm_pos_iff.2 hy0
  have hTbdd : Bornology.IsBounded T := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2 * R / ‖y0‖, fun l hl => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, le_div_iff₀ hy0n]
    have h1 := hR _ hl
    have h2 := hR x hx
    calc |l| * ‖y0‖ = ‖l • y0‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖(x + l • y0) - x‖ := by congr 1; abel
      _ ≤ ‖x + l • y0‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hTc : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTclosed hTbdd
  have hTne : T.Nonempty := ⟨0, by simpa [hT] using hx⟩
  obtain ⟨lp, hlpT, hlpub⟩ := hTc.exists_isGreatest hTne
  obtain ⟨lm, hlmT, hlmlb⟩ := hTc.exists_isLeast hTne
  have h1T : (1:ℝ) ∈ T := by simpa [hT] using hp
  have hm1T : (-1:ℝ) ∈ T := by
    show x + (-1:ℝ) • y0 ∈ P
    rw [neg_smul, one_smul, ← sub_eq_add_neg]; exact hm
  have hlp1 : 1 ≤ lp := hlpub h1T
  have hlm1 : lm ≤ -1 := hlmlb hm1T
  have haP : x + lm • y0 ∈ P := hlmT
  have hbP : x + lp • y0 ∈ P := hlpT
  have hab : x + lm • y0 ≠ x + lp • y0 := by
    intro h
    have := smul_left_injective ℝ hy0 (add_left_cancel h)
    linarith
  have seg_of : ∀ l, lm ≤ l → l ≤ lp → x + l • y0 ∈ segment ℝ (x + lm • y0) (x + lp • y0) := by
    intro l h1 h2
    have hd : lp - lm ≠ 0 := by linarith
    refine ⟨(lp - l) / (lp - lm), (l - lm) / (lp - lm), div_nonneg (by linarith) (by linarith),
      div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
    match_scalars <;> field_simp <;> ring
  have of_seg : ∀ z ∈ segment ℝ (x + lm • y0) (x + lp • y0),
      ∃ l, lm ≤ l ∧ l ≤ lp ∧ z = x + l • y0 := by
    rintro z ⟨s, t, hs, ht, hst, rfl⟩
    have hlmlp : lm ≤ lp := by linarith
    have e1 := mul_le_mul_of_nonneg_left hlmlp ht
    have e2 := mul_le_mul_of_nonneg_left hlmlp hs
    refine ⟨s * lm + t * lp, by nlinarith, by nlinarith, ?_⟩
    obtain rfl : t = 1 - s := by linarith
    module
  refine ⟨x + lm • y0, x + lp • y0, ⟨hab, ⟨hPv.segment_subset haP hbP, ?_⟩⟩, ?_, ?_⟩
  · intro p hpP q hqP z hz hzo
    obtain ⟨lz, hlz1, hlz2, rfl⟩ := of_seg z hz
    obtain ⟨s, t, hs, ht, hst, hzeq⟩ := hzo
    set κ := L (p - (x + lz • y0)) / L y0 with hκ
    set w' := p - (x + lz • y0) - κ • y0 with hw'
    have hLw' : L w' = 0 := by
      rw [hw', map_sub, map_smul, smul_eq_mul, hκ, div_mul_cancel₀ _ hLy0, sub_self]
    have hp' : p = x + w' + (lz + κ) • y0 := by
      rw [hw']; module
    have hq' : q = x + (-(s / t)) • w' + (lz - (s / t) * κ) • y0 := by
      have ht0 : t ≠ 0 := ht.ne'
      apply smul_right_injective E ht0
      have htq : t • q = x + lz • y0 - s • p := by rw [← hzeq]; abel
      simp only
      rw [htq, hp']
      obtain rfl : s = 1 - t := by linarith
      match_scalars <;> field_simp <;> ring
    obtain ⟨ε₁, hε₁, hP1⟩ := slack hPv hline hpP hp'
    obtain ⟨ε₂, hε₂, hP2⟩ := slack hPv hline hqP hq'
    have hw'0 : w' = 0 := by
      have hc : 0 < ε₂ * (s / t) / ε₁ := by positivity
      have h2 : x - (ε₂ * (s / t) / ε₁) • (ε₁ • w') ∈ P := by
        convert hP2 using 1
        have : ε₁ ≠ 0 := hε₁.ne'
        have : t ≠ 0 := ht.ne'
        match_scalars <;> field_simp <;> ring
      have := hS (ε₁ • w') hP1 _ hc h2 (by rw [map_smul, hLw', smul_zero])
      rcases smul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hpT : lz + κ ∈ T := by
      show x + (lz + κ) • y0 ∈ P
      have := hpP
      rw [hp', hw'0, add_zero] at this
      exact this
    rw [hp', hw'0, add_zero]
    exact seg_of (lz + κ) (hlmlb hpT) (hlpub hpT)
  · simpa using seg_of 0 (by linarith) (by linarith)
  · intro h
    simp only [map_add, map_smul, smul_eq_mul] at h
    have : (lp - lm) * L y0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hLy0 h'

theorem cross_eq (h : E →ᵃ[ℝ] ℝ) {a b x : E} (hx : x ∈ segment ℝ a b) (hab : h a ≠ h b) :
    x = AffineMap.lineMap a b ((h x - h a) / (h b - h a)) := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨τ, _, rfl⟩ := hx
  have e : h (AffineMap.lineMap a b τ) = h a + τ * (h b - h a) := by
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring']; ring
  have hd : h b - h a ≠ 0 := sub_ne_zero.2 hab.symm
  congr 1
  rw [e]; field_simp; ring

theorem slice_cover {P : Set E} (hPc : IsCompact P) (hPv : Convex ℝ P) (h : E →ᵃ[ℝ] ℝ)
    {v e : ℕ} (hV : VertexCover P v) (hE : EdgeCover P e) (θ : ℝ) :
    ∃ f : Fin v ⊕ Fin e → E, ({y ∈ P | h y = θ}).extremePoints ℝ ⊆ Set.range f := by
  obtain ⟨vert, hvert⟩ := hV
  obtain ⟨edges, _, hedges2⟩ := hE
  let cross : E × E → E := fun ab =>
    AffineMap.lineMap ab.1 ab.2 ((θ - h ab.1) / (h ab.2 - h ab.1))
  refine ⟨Sum.elim vert (fun j => cross (edges j)), ?_⟩
  intro x hx
  have hxP : x ∈ P := hx.1.1
  have hxθ : h x = θ := hx.1.2
  by_cases hxe : x ∈ P.extremePoints ℝ
  · obtain ⟨j, hj⟩ := hvert x hxe
    exact ⟨Sum.inl j, hj⟩
  · have hS : ∀ y : E, x + y ∈ P → ∀ c : ℝ, 0 < c → x - c • y ∈ P → h.linear y = 0 →
        y = 0 := by
      intro y hy c hc hy2 hLy
      have hmem1 : x + y ∈ {y ∈ P | h y = θ} := ⟨hy, by rw [aff_add, hLy, add_zero, hxθ]⟩
      have hmem2 : x - c • y ∈ {y ∈ P | h y = θ} := by
        refine ⟨hy2, ?_⟩
        rw [sub_eq_add_neg, aff_add, map_neg, map_smul, hLy, smul_zero, neg_zero, add_zero, hxθ]
      have hc1 : (1 + c) ≠ 0 := (by positivity : (0:ℝ) < 1 + c).ne'
      have hseg : x ∈ openSegment ℝ (x + y) (x - c • y) := by
        refine ⟨c / (1 + c), 1 / (1 + c), by positivity, by positivity, by field_simp <;> ring, ?_⟩
        match_scalars <;> field_simp <;> ring
      have := hx.2 hmem1 hmem2 hseg
      simpa using this
    obtain ⟨a, b, hab, hxab, hLab⟩ := slice_edge hPc hPv h.linear hxP hS hxe
    have hhab : h a ≠ h b := by
      intro heq
      apply hLab
      have e1 := aff_add h a (b - a)
      rw [add_sub_cancel, ← heq] at e1
      have e2 : h.linear (b - a) = 0 := by linarith
      rw [map_sub] at e2; linarith
    obtain ⟨j, hj⟩ := hedges2 a b hab
    refine ⟨Sum.inr j, ?_⟩
    simp only [Sum.elim_inr, cross]
    rcases hj with hj | hj
    · rw [hj, ← hxθ]; exact (cross_eq h hxab hhab).symm
    · rw [hj, ← hxθ]
      rw [segment_symm] at hxab
      exact (cross_eq h hxab hhab.symm).symm

theorem slice_compact [FiniteDimensional ℝ E] {P : Set E} (hPc : IsCompact P)
    (h : E →ᵃ[ℝ] ℝ) (θ : ℝ) : IsCompact {y ∈ P | h y = θ} := by
  have hcl : IsClosed (P ∩ {y | h y = θ}) :=
    hPc.isClosed.inter (isClosed_eq h.continuous_of_finiteDimensional continuous_const)
  exact hPc.of_isClosed_subset hcl Set.inter_subset_left

theorem slice_convex {P : Set E} (hPv : Convex ℝ P) (h : E →ᵃ[ℝ] ℝ) (θ : ℝ) :
    Convex ℝ {y ∈ P | h y = θ} := by
  intro a ha b hb s t hs ht hst
  refine ⟨hPv ha.1 hb.1 hs ht hst, ?_⟩
  rw [Convex.combo_affine_apply hst, ha.2, hb.2, smul_eq_mul, smul_eq_mul, ← add_mul, hst,
    one_mul]

end slices

/-! ## Faces of products -/

theorem adj_pi {ι E' : Type*} [DecidableEq ι] [AddCommGroup E'] [Module ℝ E'] {S : ι → Set E'}
    {x : ι → E'} (hx : ∀ j, x j ∈ (S j).extremePoints ℝ) (i : ι) {a b : E'}
    (hab : Adj (S i) a b) :
    Adj (Set.pi Set.univ S) (Function.update x i a) (Function.update x i b) := by
  refine ⟨fun h => hab.1 (by simpa using congrFun h i), ⟨?_, ?_⟩⟩
  · rw [← Pi.image_update_segment]
    rintro z ⟨c, hc, rfl⟩ j -
    by_cases hj : j = i
    · subst hj; simpa using hab.2.subset hc
    · simpa [Function.update_of_ne hj] using (hx j).1
  · intro p hp q hq z hz hzo
    rw [← Pi.image_update_segment] at hz ⊢
    obtain ⟨c, hc, rfl⟩ := hz
    have hcoord : ∀ j, (Function.update x i c) j ∈ openSegment ℝ (p j) (q j) := by
      intro j
      obtain ⟨s, t, hs, ht, hst, he⟩ := hzo
      exact ⟨s, t, hs, ht, hst, by rw [← he]; rfl⟩
    have hpi : p i ∈ segment ℝ a b := by
      have := hcoord i
      rw [Function.update_self] at this
      exact hab.2.left_mem_of_mem_openSegment (hp i (Set.mem_univ i)) (hq i (Set.mem_univ i))
        hc this
    refine ⟨p i, hpi, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      have := hcoord j
      rw [Function.update_of_ne hj] at this
      exact ((hx j).2 (hp j (Set.mem_univ j)) (hq j (Set.mem_univ j)) this).symm

/-! ## The scalar-height fiber -/

section fiber
variable {d k : ℕ}

theorem not_ext_of_perturb {P : Fin k → Set (EuclideanSpace ℝ (Fin d))}
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) {u z : Fin k → EuclideanSpace ℝ (Fin d)}
    (huF : u ∈ ScalarHeightFiber P h) (c : ℝ)
    (hp : ∀ i, u i + z i ∈ P i) (hm : ∀ i, u i - z i ∈ P i)
    (hc : ∀ i, (h i).linear (z i) = c) (hz : z ≠ 0) :
    u ∉ (ScalarHeightFiber P h).extremePoints ℝ := by
  intro hu
  have h1 : u + z ∈ ScalarHeightFiber P h := by
    refine ⟨fun i => hp i, fun i j => ?_⟩
    simp only [Pi.add_apply]
    rw [aff_add, aff_add, hc, hc, huF.2 i j]
  have h2 : u - z ∈ ScalarHeightFiber P h := by
    refine ⟨fun i => hm i, fun i j => ?_⟩
    simp only [Pi.sub_apply]
    rw [sub_eq_add_neg, sub_eq_add_neg, aff_add, aff_add, map_neg, map_neg, hc, hc, huF.2 i j]
  have hseg : u ∈ openSegment ℝ (u + z) (u - z) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
  have := hu.2 h1 h2 hseg
  exact hz (by simpa using this)

theorem fiber_vertex (hk : 0 < k) {P : Fin k → Set (EuclideanSpace ℝ (Fin d))}
    (hPv : ∀ i, Convex ℝ (P i)) (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
    {u : Fin k → EuclideanSpace ℝ (Fin d)} (hu : u ∈ (ScalarHeightFiber P h).extremePoints ℝ) :
    ∃ i, u i ∈ (P i).extremePoints ℝ := by
  by_contra hcon
  push Not at hcon
  have huF := hu.1
  choose y hy0 hyp hym using fun i => two_sided (hPv i) (huF.1 i) (hcon i)
  by_cases hz : ∃ i, (h i).linear (y i) = 0
  · obtain ⟨i, hi⟩ := hz
    refine not_ext_of_perturb h huF 0 (z := Pi.single i (y i)) ?_ ?_ ?_ ?_ hu
    · intro j
      by_cases hji : j = i
      · subst hji; simpa using hyp j
      · simpa [Pi.single_apply, hji] using huF.1 j
    · intro j
      by_cases hji : j = i
      · subst hji; simpa using hym j
      · simpa [Pi.single_apply, hji] using huF.1 j
    · intro j
      by_cases hji : j = i
      · subst hji; simpa using hi
      · simp [Pi.single_apply, hji]
    · intro h0
      apply hy0 i
      have := congrFun h0 i
      simpa using this
  · push Not at hz
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    set c := Finset.univ.inf' hne (fun i => |(h i).linear (y i)|) with hcdef
    have hc0 : 0 < c := by
      rw [hcdef, Finset.lt_inf'_iff]; intro i _; exact abs_pos.2 (hz i)
    have hcle : ∀ i, c ≤ |(h i).linear (y i)| := fun i => Finset.inf'_le _ (Finset.mem_univ i)
    have hratio : ∀ i, |c / (h i).linear (y i)| ≤ 1 := by
      intro i
      rw [abs_div, abs_of_pos hc0, div_le_one (abs_pos.2 (hz i))]
      exact hcle i
    refine not_ext_of_perturb h huF c (z := fun i => (c / (h i).linear (y i)) • y i)
      ?_ ?_ ?_ ?_ hu
    · intro i
      exact line_mem (hPv i) (hyp i) (hym i) _ (neg_le_of_abs_le (hratio i))
        (le_of_abs_le (hratio i))
    · intro i
      have := line_mem (hPv i) (hyp i) (hym i) (-(c / (h i).linear (y i)))
        (by have := le_of_abs_le (hratio i); linarith)
        (by have := neg_le_of_abs_le (hratio i); linarith)
      show u i - (c / (h i).linear (y i)) • y i ∈ P i
      rw [sub_eq_add_neg, ← neg_smul]; exact this
    · intro i
      simp only [map_smul, smul_eq_mul]
      field_simp [hz i]
    · intro h0
      have := congrFun h0 ⟨0, hk⟩
      simp only [Pi.zero_apply, smul_eq_zero] at this
      rcases this with h1 | h1
      · rw [div_eq_zero_iff] at h1
        rcases h1 with h1 | h1
        · linarith
        · exact hz _ h1
      · exact hy0 _ h1

theorem fiber_convex {P : Fin k → Set (EuclideanSpace ℝ (Fin d))} (hPv : ∀ i, Convex ℝ (P i))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) : Convex ℝ (ScalarHeightFiber P h) := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun i => hPv i (hx.1 i) (hy.1 i) hs ht hst, fun i j => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [Convex.combo_affine_apply hst, Convex.combo_affine_apply hst, hx.2 i j, hy.2 i j]

theorem fiber_compact {P : Fin k → Set (EuclideanSpace ℝ (Fin d))}
    (hPc : ∀ i, IsCompact (P i)) (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    IsCompact (ScalarHeightFiber P h) := by
  have hpi : IsCompact (Set.pi Set.univ P) := isCompact_univ_pi hPc
  have heq : ScalarHeightFiber P h = Set.pi Set.univ P ∩
      ⋂ i, ⋂ j, {x : Fin k → EuclideanSpace ℝ (Fin d) | h i (x i) = h j (x j)} := by
    ext x; simp [ScalarHeightFiber, Set.mem_pi]
  rw [heq]
  refine hpi.of_isClosed_subset ?_ Set.inter_subset_left
  refine hpi.isClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  exact isClosed_eq (((h i).continuous_of_finiteDimensional).comp (continuous_apply i))
    (((h j).continuous_of_finiteDimensional).comp (continuous_apply j))

theorem top_face {P : Fin k → Set (EuclideanSpace ℝ (Fin d))}
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) (i0 : Fin k) (θ : ℝ)
    (hmax : ∀ x ∈ ScalarHeightFiber P h, h i0 (x i0) ≤ θ) :
    IsExtreme ℝ (ScalarHeightFiber P h) (Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ})) := by
  have hsub : Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ}) ⊆ ScalarHeightFiber P h := by
    intro x hx
    refine ⟨fun i => (hx i (Set.mem_univ i)).1, fun i j => ?_⟩
    rw [(hx i (Set.mem_univ i)).2, (hx j (Set.mem_univ j)).2]
  refine ⟨hsub, ?_⟩
  intro p hp q hq z hz hzo
  have hzθ : h i0 (z i0) = θ := (hz i0 (Set.mem_univ _)).2
  obtain ⟨s, t, hs, ht, hst, he⟩ := hzo
  have hz0 : z i0 = s • p i0 + t • q i0 := by rw [← he]; rfl
  have hcomb : h i0 (z i0) = s * h i0 (p i0) + t * h i0 (q i0) := by
    rw [hz0, Convex.combo_affine_apply hst, smul_eq_mul, smul_eq_mul]
  have hp0 := hmax p hp
  have hq0 := hmax q hq
  have hpθ : h i0 (p i0) = θ := by
    by_contra hne
    have hlt : h i0 (p i0) < θ := lt_of_le_of_ne hp0 hne
    have e1 := mul_pos hs (sub_pos.2 hlt)
    have e2 := mul_nonneg ht.le (sub_nonneg.2 hq0)
    rw [hzθ] at hcomb
    have e3 : s * θ + t * θ = θ := by rw [← add_mul, hst, one_mul]
    nlinarith
  intro i _
  refine ⟨hp.1 i, ?_⟩
  rw [hp.2 i i0, hpθ]

theorem main_pos (hk : 0 < k) (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) (v e : Fin k → ℕ)
    (hPv : ∀ i, Convex ℝ (P i)) (hPc : ∀ i, IsCompact (P i))
    (hV : ∀ i, VertexCover (P i) (v i)) (hE : ∀ i, EdgeCover (P i) (e i)) :
    DiamLE (ScalarHeightFiber P h) (∑ i, (3 * v i + e i - 1)) := by
  classical
  have hFc : IsCompact (ScalarHeightFiber P h) := fiber_compact hPc h
  have hFv : Convex ℝ (ScalarHeightFiber P h) := fiber_convex hPv h
  choose vert hvert using hV
  have hcov : ∀ i θ, ∃ f : Fin (v i) ⊕ Fin (e i) → EuclideanSpace ℝ (Fin d),
      ({y ∈ P i | h i y = θ}).extremePoints ℝ ⊆ Set.range f :=
    fun i θ => slice_cover (hPc i) (hPv i) (h i) ⟨vert i, hvert i⟩ (hE i) θ
  have hslfin : ∀ i θ, (({y ∈ P i | h i y = θ}).extremePoints ℝ).Finite := by
    intro i θ
    obtain ⟨f, hf⟩ := hcov i θ
    exact (Set.finite_range f).subset hf
  have hext_slice : ∀ u ∈ (ScalarHeightFiber P h).extremePoints ℝ, ∀ θ,
      (∀ i, h i (u i) = θ) → ∀ i, u i ∈ ({y ∈ P i | h i y = θ}).extremePoints ℝ := by
    intro u hu θ hθ
    have hsub : Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ}) ⊆ ScalarHeightFiber P h := by
      intro x hx
      refine ⟨fun i => (hx i (Set.mem_univ i)).1, fun i j => ?_⟩
      rw [(hx i (Set.mem_univ i)).2, (hx j (Set.mem_univ j)).2]
    have hupi : u ∈ Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ}) :=
      fun i _ => ⟨hu.1.1 i, hθ i⟩
    have := inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hupi, hu⟩
    rw [extremePoints_pi] at this
    exact fun i => this i (Set.mem_univ i)
  have hvh : ∀ u ∈ (ScalarHeightFiber P h).extremePoints ℝ,
      ∃ p : (Σ i, Fin (v i)), ∀ i, h i (u i) = h p.1 (vert p.1 p.2) := by
    intro u hu
    obtain ⟨i, hi⟩ := fiber_vertex hk hPv h hu
    obtain ⟨j, hj⟩ := hvert i (u i) hi
    exact ⟨⟨i, j⟩, fun i' => by rw [hu.1.2 i' i, hj]⟩
  have hFfin : ((ScalarHeightFiber P h).extremePoints ℝ).Finite := by
    have hsub : (ScalarHeightFiber P h).extremePoints ℝ ⊆ ⋃ p : (Σ i, Fin (v i)),
        Set.pi Set.univ
          (fun i => ({y ∈ P i | h i y = h p.1 (vert p.1 p.2)}).extremePoints ℝ) := by
      intro u hu
      obtain ⟨p, hp⟩ := hvh u hu
      exact Set.mem_iUnion.2 ⟨p, fun i _ => hext_slice u hu _ hp i⟩
    exact Set.Finite.subset (Set.finite_iUnion fun p => Set.Finite.pi fun i => hslfin i _) hsub
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  set φ : (Fin k → EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((h i0).linear ∘ₗ LinearMap.proj i0) with hφ
  have hφapp : ∀ x, φ x = (h i0).linear (x i0) := fun x => rfl
  have hh0 : ∀ x : EuclideanSpace ℝ (Fin d), h i0 x = h i0 0 + (h i0).linear x := by
    intro x; have := aff_add (h i0) 0 x; rwa [zero_add] at this
  set Φ : Finset ℝ :=
    Finset.univ.image (fun p : (Σ i, Fin (v i)) => h p.1 (vert p.1 p.2) - h i0 0) with hΦdef
  have hΦ : ∀ y ∈ (ScalarHeightFiber P h).extremePoints ℝ, φ y ∈ Φ := by
    intro y hy
    obtain ⟨p, hp⟩ := hvh y hy
    refine Finset.mem_image.2 ⟨p, Finset.mem_univ _, ?_⟩
    rw [hφapp, ← hp i0, hh0]; ring
  have hΦcard : Φ.card ≤ ∑ i, v i := by
    refine Finset.card_image_le.trans ?_
    simp [Finset.card_univ, Fintype.card_sigma]
  have hasc : ∀ u ∈ (ScalarHeightFiber P h).extremePoints ℝ,
      ∃ u' ∈ (ScalarHeightFiber P h).extremePoints ℝ,
        (∀ y ∈ ScalarHeightFiber P h, φ y ≤ φ u') ∧
        EndpointWalkLE (ScalarHeightFiber P h) (∑ i, v i) u u' := by
    intro u hu
    obtain ⟨u', hu', hmax, hw⟩ :=
      path hFc hFv hFfin φ Φ hΦ Φ.card u hu (Finset.card_filter_le _ _)
    exact ⟨u', hu', hmax, walk_mono hΦcard hw⟩
  intro u hu w hw
  obtain ⟨u', hu', humax, hwu⟩ := hasc u hu
  obtain ⟨w', hw', hwmax, hww⟩ := hasc w hw
  have hφeq : φ u' = φ w' := le_antisymm (hwmax u' hu'.1) (humax w' hw'.1)
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = h i0 (u' i0) := ⟨_, rfl⟩
  have hmaxθ : ∀ x ∈ ScalarHeightFiber P h, h i0 (x i0) ≤ θ := by
    intro x hx
    have h1 := humax x hx
    rw [hφapp, hφapp] at h1
    rw [hθ, hh0 (x i0), hh0 (u' i0)]
    linarith
  have htop := top_face h i0 θ hmaxθ
  have hu'θ : ∀ i, h i (u' i) = θ := fun i => (hu'.1.2 i i0).trans hθ.symm
  have hw'θ : ∀ i, h i (w' i) = θ := by
    intro i
    rw [hw'.1.2 i i0, hθ, hh0 (w' i0), hh0 (u' i0)]
    have := hφeq
    rw [hφapp, hφapp] at this
    linarith
  have hu'S : ∀ i, u' i ∈ ({y ∈ P i | h i y = θ}).extremePoints ℝ :=
    hext_slice u' hu' θ hu'θ
  have hw'S : ∀ i, w' i ∈ ({y ∈ P i | h i y = θ}).extremePoints ℝ :=
    hext_slice w' hw' θ hw'θ
  have hwalkS : ∀ i, EndpointWalkLE {y ∈ P i | h i y = θ} (v i + e i - 1) (u' i) (w' i) := by
    intro i
    have hSc : IsCompact {y ∈ P i | h i y = θ} := slice_compact (hPc i) (h i) θ
    have hSv : Convex ℝ {y ∈ P i | h i y = θ} := slice_convex (hPv i) (h i) θ
    obtain ⟨f, hf⟩ := hcov i θ
    have hSfin := hslfin i θ
    obtain ⟨g, hg⟩ := exposed hSc hSv hSfin (hw'S i)
    set Ψ : Finset ℝ := Finset.univ.image (fun j => g (f j)) with hΨdef
    have hΨ : ∀ y ∈ ({y ∈ P i | h i y = θ}).extremePoints ℝ, g y ∈ Ψ := by
      intro y hy
      obtain ⟨j, hj⟩ := hf hy
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, by rw [hj]⟩
    have hcard : (Ψ.filter (fun t => g (u' i) < t)).card ≤ v i + e i - 1 := by
      have h1 : Ψ.filter (fun t => g (u' i) < t) ⊆ Ψ.erase (g (u' i)) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        exact Finset.mem_erase.2 ⟨ht.2.ne', ht.1⟩
      have h2 : (Ψ.erase (g (u' i))).card = Ψ.card - 1 :=
        Finset.card_erase_of_mem (hΨ _ (hu'S i))
      have h3 : Ψ.card ≤ v i + e i := by
        refine Finset.card_image_le.trans ?_
        simp
      have := Finset.card_le_card h1
      omega
    obtain ⟨x'', hx'', hmax'', hwalk⟩ := path hSc hSv hSfin g Ψ hΨ _ (u' i) (hu'S i) hcard
    have hx''eq : x'' = w' i := by
      by_contra hne
      have e1 := hg x'' hx''.1 hne
      have e2 := hmax'' (w' i) (hw'S i).1
      linarith
    rw [hx''eq] at hwalk
    exact hwalk
  have hprod : ∀ s : Finset (Fin k),
      EndpointWalkLE (Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ}))
        (∑ i ∈ s, (v i + e i - 1)) u' (s.piecewise w' u') := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using walk_refl (Set.pi Set.univ (fun i => {y ∈ P i | h i y = θ})) 0 u'
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.piecewise_insert]
      have hx : ∀ j, (s.piecewise w' u') j ∈ ({y ∈ P j | h j y = θ}).extremePoints ℝ := by
        intro j
        by_cases hj : j ∈ s
        · rw [Finset.piecewise_eq_of_mem _ _ _ hj]; exact hw'S j
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hj]; exact hu'S j
      have hl := walk_map (Function.update (s.piecewise w' u') a)
        (fun p q hpq => adj_pi hx a hpq) (hwalkS a)
      have e1 : Function.update (s.piecewise w' u') a (u' a) = s.piecewise w' u' := by
        have : u' a = (s.piecewise w' u') a := (Finset.piecewise_eq_of_notMem _ _ _ ha).symm
        rw [this]
        exact Function.update_eq_self _ _
      rw [e1] at hl
      exact walk_mono (by omega) (walk_trans ih hl)
  have hmid : EndpointWalkLE (ScalarHeightFiber P h) (∑ i, (v i + e i - 1)) u' w' := by
    have := hprod Finset.univ
    rw [Finset.piecewise_univ] at this
    exact walk_of_face htop this
  have htot := walk_trans (walk_trans hwu hmid) (walk_symm hww)
  have hsum : ∑ i, (3 * v i + e i - 1) = ∑ i, v i + ∑ i, (v i + e i - 1) + ∑ i, v i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by omega)
  rw [hsum]
  exact htot

end fiber

end P2Mb372

set_option maxHeartbeats 4000000 in
open scoped RealInnerProductSpace BigOperators in
theorem solution :
    ∀ (k d : ℕ)
      (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
      (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
      (v e : Fin k → ℕ),
      (∀ i, Convex ℝ (P i)) →
      (∀ i, IsCompact (P i)) →
      (∀ i, (P i).Nonempty) →
      (∀ i, Hirsch.VertexCover (P i) (v i)) →
      (∀ i, Hirsch.EdgeCover (P i) (e i)) →
      Hirsch.DiamLE (Hirsch.ScalarHeightFiber P h)
        (∑ i, (3 * v i + e i - 1)) := by
  intro k d P h v e hconv hcomp _ hV hE
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    intro u _ w _
    have huw : u = w := Subsingleton.elim _ _
    subst huw
    exact P2Mb372.walk_refl (Hirsch.ScalarHeightFiber P h) _ u
  · exact P2Mb372.main_pos hk P h v e hconv hcomp hV hE
