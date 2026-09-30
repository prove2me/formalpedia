-- Prove2me | solution 1 for Hirsch.scalar_height_fiber_monotone_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T13:18:41.458107+00:00
-- url     : https://prove2.me/submissions/1c589aab-ebf7-43f8-826f-98a2e38848e0

import Mathlib
import Definitions.Def_Hirsch_scalar_fiber_model

set_option autoImplicit false

open scoped RealInnerProductSpace BigOperators

namespace P2Mfcb

open Hirsch

/-! ## Walk algebra on `EndpointWalkLE` (from b372d4fc) -/

section walks
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

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

end walks

/-! ## Heights along a segment -/

section seg
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem cross_eq (h : E →ᵃ[ℝ] ℝ) {a b x : E} (hx : x ∈ segment ℝ a b) (hab : h a ≠ h b) :
    x = AffineMap.lineMap a b ((h x - h a) / (h b - h a)) := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨τ, _, rfl⟩ := hx
  have e : h (AffineMap.lineMap a b τ) = h a + τ * (h b - h a) := by
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring']; ring
  have hd : h b - h a ≠ 0 := sub_ne_zero.2 hab.symm
  congr 1
  rw [e]; field_simp; ring

theorem seg_h (f : E →ᵃ[ℝ] ℝ) {a b x : E} (hx : x ∈ segment ℝ a b) (hab : f b ≤ f a) :
    f b ≤ f x ∧ f x ≤ f a := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hx
  have e : f (AffineMap.lineMap a b τ) = f a + τ * (f b - f a) := by
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring']; ring
  rw [e]; constructor <;> nlinarith

theorem seg_uniq (f : E →ᵃ[ℝ] ℝ) {a b p q : E} (hp : p ∈ segment ℝ a b)
    (hq : q ∈ segment ℝ a b) (hab : f a ≠ f b) (hpq : f p = f q) : p = q := by
  have e1 := cross_eq f hp hab
  have e2 := cross_eq f hq hab
  rw [hpq] at e1
  exact e1.trans e2.symm

/-- The point of the line through `a b` at height `T`. -/
noncomputable def pt (f : E →ᵃ[ℝ] ℝ) (a b : E) (T : ℝ) : E :=
  AffineMap.lineMap a b ((T - f a) / (f b - f a))

theorem pt_h (f : E →ᵃ[ℝ] ℝ) {a b : E} (hab : f a ≠ f b) (T : ℝ) : f (pt f a b T) = T := by
  unfold pt
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring']
  have hd : f b - f a ≠ 0 := sub_ne_zero.2 hab.symm
  field_simp; ring

theorem pt_seg (f : E →ᵃ[ℝ] ℝ) {a b : E} (hab : f b < f a) {T : ℝ} (h1 : f b ≤ T)
    (h2 : T ≤ f a) : pt f a b T ∈ segment ℝ a b := by
  rw [segment_eq_image_lineMap]
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · rw [div_le_one_of_neg (by linarith)]; linarith

omit [AddCommGroup E] [Module ℝ E] in
theorem chain_lt (f : E → ℝ) (W : ℕ → E) (L : ℕ) (hc : ∀ j < L, f (W (j+1)) < f (W j)) :
    ∀ m, m ≤ L → ∀ j < m, f (W m) < f (W j) := by
  intro m
  induction m with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro hm j hj
    have h1 := hc m (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact h1.trans (ih (by omega) j hj)
    · subst hj; exact h1

end seg

/-! ## The fiber -/

section fiber
variable {d k : ℕ}

theorem fiber_convex {P : Fin k → Set (EuclideanSpace ℝ (Fin d))} (hPv : ∀ i, Convex ℝ (P i))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) : Convex ℝ (ScalarHeightFiber P h) := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun i => hPv i (hx.1 i) (hy.1 i) hs ht hst, fun i j => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [Convex.combo_affine_apply hst, Convex.combo_affine_apply hst, hx.2 i j, hy.2 i j]

/-- Key lemma: two fiber points lying on a product of edges, the first at the lowest top
and the second at the highest bottom, are adjacent in the fiber. -/
theorem fiber_adj {P : Fin k → Set (EuclideanSpace ℝ (Fin d))} (hPv : ∀ i, Convex ℝ (P i))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
    (a b c c' : Fin k → EuclideanSpace ℝ (Fin d))
    (hedge : ∀ i, IsExtreme ℝ (P i) (segment ℝ (a i) (b i)))
    (hab : ∀ i, h i (b i) < h i (a i))
    (hc : c ∈ ScalarHeightFiber P h) (hc' : c' ∈ ScalarHeightFiber P h)
    (hcs : ∀ i, c i ∈ segment ℝ (a i) (b i)) (hcs' : ∀ i, c' i ∈ segment ℝ (a i) (b i))
    (i0 : Fin k) (htop : h i0 (c i0) = h i0 (a i0))
    (i1 : Fin k) (hbot : h i1 (c' i1) = h i1 (b i1))
    (hlt : h i0 (c' i0) < h i0 (c i0)) :
    Adj (ScalarHeightFiber P h) c c' := by
  refine ⟨?_, ⟨(fiber_convex hPv h).segment_subset hc hc', ?_⟩⟩
  · intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt
  · intro x hx y hy z hz hzo
    have hzi : ∀ i, z i ∈ segment ℝ (a i) (b i) := by
      intro i
      have : z i ∈ segment ℝ (c i) (c' i) := by
        obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
        exact ⟨s, t, hs, ht, hst, rfl⟩
      exact (convex_segment _ _).segment_subset (hcs i) (hcs' i) this
    have hoi : ∀ i, z i ∈ openSegment ℝ (x i) (y i) := by
      intro i
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzo
      exact ⟨s, t, hs, ht, hst, rfl⟩
    have hxi : ∀ i, x i ∈ segment ℝ (a i) (b i) := fun i =>
      (hedge i).left_mem_of_mem_openSegment (hx.1 i) (hy.1 i) (hzi i) (hoi i)
    set S := h i0 (c i0) with hS
    set R := h i0 (c' i0) with hR
    set t := h i0 (x i0) with ht
    have hcS : ∀ i, h i (c i) = S := fun i => hc.2 i i0
    have hcR : ∀ i, h i (c' i) = R := fun i => hc'.2 i i0
    have hxt : ∀ i, h i (x i) = t := fun i => hx.2 i i0
    have htS : t ≤ S := by
      have := (seg_h (h i0) (hxi i0) (hab i0).le).2
      rw [htop]; exact this
    have hRt : R ≤ t := by
      have := (seg_h (h i1) (hxi i1) (hab i1).le).1
      rw [← hbot, hcR i1, hxt i1] at this; exact this
    have hSR : 0 < S - R := by linarith
    set θ := (S - t) / (S - R) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hSR.le
    have hθ1 : θ ≤ 1 := by rw [div_le_one hSR]; linarith
    have hθe : θ * (S - R) = S - t := by rw [hθ]; field_simp
    have hxe : x = (1 - θ) • c + θ • c' := by
      funext i
      have hq : ((1 - θ) • c + θ • c') i ∈ segment ℝ (a i) (b i) := by
        have : ((1 - θ) • c + θ • c') i ∈ segment ℝ (c i) (c' i) :=
          ⟨1 - θ, θ, by linarith, hθ0, by ring, rfl⟩
        exact (convex_segment _ _).segment_subset (hcs i) (hcs' i) this
      refine seg_uniq (h i) (hxi i) hq (hab i).ne' ?_
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [Convex.combo_affine_apply (by ring), hcS i, hcR i, hxt i, smul_eq_mul, smul_eq_mul]
      linarith
    rw [hxe]
    exact ⟨1 - θ, θ, by linarith, hθ0, by ring, rfl⟩


/-- Base step: all remaining walks are single edges. -/
theorem base_adj {P : Fin k → Set (EuclideanSpace ℝ (Fin d))} (hPv : ∀ i, Convex ℝ (P i))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
    (W : Fin k → ℕ → EuclideanSpace ℝ (Fin d)) (c : Fin k → EuclideanSpace ℝ (Fin d))
    (hchain : ∀ i, Adj (P i) (W i 0) (W i 1) ∧ h i (W i 1) < h i (W i 0))
    (hend : ∀ i j, h i (W i 1) = h j (W j 1))
    (hc : c ∈ ScalarHeightFiber P h) (hcs : ∀ i, c i ∈ segment ℝ (W i 0) (W i 1))
    (i0 : Fin k) (htop : h i0 (c i0) = h i0 (W i0 0)) :
    Adj (ScalarHeightFiber P h) c (fun i => W i 1) := by
  have hedge : ∀ i, IsExtreme ℝ (P i) (segment ℝ (W i 0) (W i 1)) := fun i => (hchain i).1.2
  refine fiber_adj hPv h (fun i => W i 0) (fun i => W i 1) c (fun i => W i 1) hedge
    (fun i => (hchain i).2) hc ⟨fun i => (hedge i).subset (right_mem_segment ℝ _ _), hend⟩
    hcs (fun i => right_mem_segment ℝ _ _) i0 htop i0 rfl ?_
  rw [htop]; exact (hchain i0).2

theorem gen {P : Fin k → Set (EuclideanSpace ℝ (Fin d))} (hPv : ∀ i, Convex ℝ (P i))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    ∀ (N : ℕ) (L : Fin k → ℕ) (W : Fin k → ℕ → EuclideanSpace ℝ (Fin d))
      (c : Fin k → EuclideanSpace ℝ (Fin d)),
      (∀ i, 1 ≤ L i) → (∑ i, (L i - 1)) ≤ N →
      (∀ i, ∀ j < L i, Adj (P i) (W i j) (W i (j+1)) ∧ h i (W i (j+1)) < h i (W i j)) →
      (∀ i j, h i (W i (L i)) = h j (W j (L j))) →
      c ∈ ScalarHeightFiber P h → (∀ i, c i ∈ segment ℝ (W i 0) (W i 1)) →
      (∃ i0, h i0 (c i0) = h i0 (W i0 0)) →
      EndpointWalkLE (ScalarHeightFiber P h) (1 + N) c (fun i => W i (L i)) := by
  intro N
  induction N with
  | zero =>
    intro L W c hL hsum hchain hend hc hcs htop
    obtain ⟨i0, htop⟩ := htop
    have hL1 : ∀ i, L i = 1 := by
      intro i
      have h0 : ∑ i, (L i - 1) = 0 := by omega
      have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
      have := hL i
      omega
    have hW : (fun i => W i (L i)) = (fun i => W i 1) := by funext i; rw [hL1 i]
    rw [hW]
    refine walk_single (base_adj hPv h W c (fun i => ?_) (fun i j => ?_) hc hcs i0 htop)
    · have := hchain i 0 (by rw [hL1 i]; omega); simpa using this
    · have := hend i j; rwa [hL1 i, hL1 j] at this
  | succ n ih =>
    intro L W c hL hsum hchain hend hc hcs htop
    obtain ⟨i0, htop⟩ := htop
    by_cases hall : ∀ i, L i = 1
    · have hW : (fun i => W i (L i)) = (fun i => W i 1) := by funext i; rw [hall i]
      rw [hW]
      refine walk_mono (by omega)
        (walk_single (base_adj hPv h W c (fun i => ?_) (fun i j => ?_) hc hcs i0 htop))
      · have := hchain i 0 (by rw [hall i]; omega); simpa using this
      · have := hend i j; rwa [hall i, hall j] at this
    · push Not at hall
      obtain ⟨i2, hi2⟩ := hall
      have hne : (Finset.univ.filter (fun i => 2 ≤ L i)).Nonempty :=
        ⟨i2, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := hL i2; omega⟩
      obtain ⟨m, hmmem, hmax⟩ := Finset.exists_max_image _ (fun i => h i (W i 1)) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmmem hmax
      set T := h m (W m 1) with hT
      set S := h i0 (c i0) with hS
      have hcS : ∀ i, h i (c i) = S := fun i => hc.2 i i0
      have hab : ∀ i, h i (W i 1) < h i (W i 0) := fun i => (hchain i 0 (by have := hL i; omega)).2
      have hedge : ∀ i, IsExtreme ℝ (P i) (segment ℝ (W i 0) (W i 1)) :=
        fun i => (hchain i 0 (by have := hL i; omega)).1.2
      have hbd : ∀ i, h i (W i 1) ≤ h i (c i) ∧ h i (c i) ≤ h i (W i 0) :=
        fun i => seg_h (h i) (hcs i) (hab i).le
      have hTS : T ≤ S := by rw [← hcS m]; exact (hbd m).1
      have hTlo : ∀ i, h i (W i 1) ≤ T := by
        intro i
        by_cases h2 : 2 ≤ L i
        · exact hmax i h2
        · have hLi : L i = 1 := by have := hL i; omega
          have e1 : h i (W i 1) = h m (W m (L m)) := by
            have := hend i m; rwa [hLi] at this
          rw [e1]
          have := chain_lt (fun x => h m x) (W m) (L m) (fun j hj => (hchain m j hj).2) (L m)
            le_rfl 1 (by omega)
          exact this.le
      set c' : Fin k → EuclideanSpace ℝ (Fin d) := fun i => pt (h i) (W i 0) (W i 1) T with hc'def
      have hc'h : ∀ i, h i (c' i) = T := fun i => pt_h (h i) (hab i).ne' T
      have hc's : ∀ i, c' i ∈ segment ℝ (W i 0) (W i 1) := fun i =>
        pt_seg (h i) (hab i) (hTlo i) (by rw [← hcS i] at hTS; exact hTS.trans (hbd i).2)
      have hc'Q : c' ∈ ScalarHeightFiber P h :=
        ⟨fun i => (hedge i).subset (hc's i), fun i j => by rw [hc'h, hc'h]⟩
      have hc'm : c' m = W m 1 :=
        seg_uniq (h m) (hc's m) (right_mem_segment ℝ _ _) (hab m).ne' (by rw [hc'h])
      have hstep : c = c' ∨ Adj (ScalarHeightFiber P h) c c' := by
        by_cases hTS' : T = S
        · left
          funext i
          exact seg_uniq (h i) (hcs i) (hc's i) (hab i).ne' (by rw [hcS, hc'h, hTS'])
        · right
          refine fiber_adj hPv h (fun i => W i 0) (fun i => W i 1) c c' hedge hab hc hc'Q hcs hc's
            i0 htop m (by rw [hc'h]) ?_
          rw [hc'h]; exact lt_of_le_of_ne hTS hTS'
      -- the new configuration
      set L' : Fin k → ℕ := fun i => if i = m then L i - 1 else L i with hL'def
      set W' : Fin k → ℕ → EuclideanSpace ℝ (Fin d) :=
        fun i => if i = m then (fun j => W i (j+1)) else W i with hW'def
      have hWL : ∀ i, W' i (L' i) = W i (L i) := by
        intro i
        by_cases hi : i = m
        · subst hi; simp only [hL'def, hW'def, if_true]
          rw [show L i - 1 + 1 = L i by omega]
        · simp only [hL'def, hW'def, hi, if_false]
      have hW'0 : ∀ i, i ≠ m → W' i = W i := fun i hi => by simp only [hW'def, hi, if_false]
      have hL'1 : ∀ i, i ≠ m → L' i = L i := fun i hi => by simp only [hL'def, hi, if_false]
      have hW'm : W' m = fun j => W m (j+1) := by simp only [hW'def, if_true]
      have hL'm : L' m = L m - 1 := by simp only [hL'def, if_true]
      have hsum' : ∑ i, (L' i - 1) ≤ n := by
        have e1 := (Finset.add_sum_erase Finset.univ (fun i => L i - 1) (Finset.mem_univ m))
        have e2 := (Finset.add_sum_erase Finset.univ (fun i => L' i - 1) (Finset.mem_univ m))
        have e3 : ∑ i ∈ Finset.univ.erase m, (L' i - 1) = ∑ i ∈ Finset.univ.erase m, (L i - 1) :=
          Finset.sum_congr rfl (fun i hi => by rw [hL'1 i (Finset.ne_of_mem_erase hi)])
        simp only at e1 e2
        rw [hL'm] at e2
        omega
      have hrest := ih L' W' c' (fun i => by
          by_cases hi : i = m
          · subst hi; rw [hL'm]; omega
          · rw [hL'1 i hi]; exact hL i) hsum'
        (fun i j hj => by
          by_cases hi : i = m
          · subst hi; rw [hW'm]; rw [hL'm] at hj
            exact hchain i (j+1) (by omega)
          · rw [hW'0 i hi]; rw [hL'1 i hi] at hj; exact hchain i j hj)
        (fun i j => by rw [hWL, hWL]; exact hend i j) hc'Q
        (fun i => by
          by_cases hi : i = m
          · subst hi; rw [hW'm, hc'm]; exact left_mem_segment ℝ _ _
          · rw [hW'0 i hi]; exact hc's i)
        ⟨m, by rw [hW'm, hc'm]⟩
      have hWe : (fun i => W' i (L' i)) = (fun i => W i (L i)) := funext hWL
      rw [hWe] at hrest
      rcases hstep with hst | hst
      · rw [hst]; exact walk_mono (by omega) hrest
      · exact walk_mono (by omega) (walk_trans (walk_single hst) hrest)

end fiber

end P2Mfcb

set_option maxHeartbeats 4000000 in
open scoped RealInnerProductSpace BigOperators in
theorem solution :
    ∀ (k d : ℕ)
      (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
      (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
      (L : Fin k → ℕ)
      (u v : Fin k → EuclideanSpace ℝ (Fin d)),
      (∀ i, Convex ℝ (P i)) →
      (∀ i, Hirsch.StrictHeightEdgeWalk (P i) (h i) (L i) (u i) (v i)) →
      (∀ i j, h i (u i) = h j (u j)) →
      (∀ i j, h i (v i) = h j (v j)) →
      Hirsch.EndpointWalkLE (Hirsch.ScalarHeightFiber P h)
        (1 + ∑ i, (L i - 1)) u v := by
  intro k d P h L u v hconv hwalk hu hv
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have huv : u = v := Subsingleton.elim _ _
    subst huv
    exact P2Mfcb.walk_refl _ _ u
  choose w hw0 hwL hwP hwstep using hwalk
  let W : Fin k → ℕ → EuclideanSpace ℝ (Fin d) :=
    fun i j => w i ⟨min j (L i), Nat.lt_succ_of_le (min_le_right j (L i))⟩
  have hWj : ∀ i j (hj : j ≤ L i), W i j = w i ⟨j, Nat.lt_succ_of_le hj⟩ := by
    intro i j hj
    simp only [W]
    congr 1
    ext
    simp only
    exact min_eq_left hj
  have hW0 : ∀ i, W i 0 = u i := fun i => by rw [hWj i 0 (Nat.zero_le _)]; exact hw0 i
  have hWL : ∀ i, W i (L i) = v i := fun i => by rw [hWj i (L i) le_rfl]; exact hwL i
  have hstep : ∀ i, ∀ j < L i,
      Hirsch.Adj (P i) (W i j) (W i (j+1)) ∧ h i (W i (j+1)) < h i (W i j) := by
    intro i j hj
    have := hwstep i ⟨j, hj⟩
    rw [hWj i j hj.le, hWj i (j+1) hj]
    exact ⟨this.1, this.2⟩
  have hPu : ∀ i, u i ∈ P i := fun i => by rw [← hw0 i]; exact hwP i _
  have hvW : (fun i => W i (L i)) = v := funext hWL
  by_cases hL0 : ∃ i, L i = 0
  · obtain ⟨i1, hi1⟩ := hL0
    have hHuv : h i1 (u i1) = h i1 (v i1) := by
      rw [← hW0, ← hWL, hi1]
    have hall : ∀ j, u j = v j := by
      intro j
      by_cases hj : L j = 0
      · rw [← hW0, ← hWL, hj]
      · exfalso
        have hlt := P2Mfcb.chain_lt (fun x => h j x) (W j) (L j) (fun m hm => (hstep j m hm).2)
          (L j) le_rfl 0 (by omega)
        simp only [hW0, hWL] at hlt
        rw [hu j i1, hv j i1, hHuv] at hlt
        exact lt_irrefl _ hlt
    have huv : u = v := funext hall
    subst huv
    exact P2Mfcb.walk_refl _ _ u
  · push Not at hL0
    have hL : ∀ i, 1 ≤ L i := fun i => Nat.one_le_iff_ne_zero.2 (hL0 i)
    have key := P2Mfcb.gen hconv h (∑ i, (L i - 1)) L W u hL le_rfl hstep
      (fun i j => by rw [hWL, hWL]; exact hv i j)
      ⟨hPu, hu⟩ (fun i => by rw [hW0]; exact left_mem_segment ℝ _ _)
      ⟨⟨0, hk⟩, by rw [hW0]⟩
    rw [hvW] at key
    exact key
