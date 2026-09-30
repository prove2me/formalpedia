-- Prove2me | solution 1 for Hirsch.exposed_core_edge_has_minkowski_bridge
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T01:15:26.516224+00:00
-- url     : https://prove2.me/submissions/c2872155-4d73-4bdd-b9bd-153dab8c619e

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace HirschEdgeLift
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Vanishing on the generator implies vanishing on its entire span. -/
private lemma annihilates_span (e : E) (f : E →ₗ[ℝ] ℝ) (hf : f e = 0)
    {x : E} (hx : x ∈ Submodule.span ℝ ({e} : Set E)) : f x = 0 := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
  rw [← ht, map_smul, hf, smul_zero]

/-- A generic perturbation in the annihilator preserves all originally strict
finite comparisons, and ties exactly the listed directions parallel to e. -/
theorem generic_edge_objective (e : E) (D : Finset E)
    (f₀ : E →ₗ[ℝ] ℝ) (h₀ : f₀ e = 0) :
    ∃ f : E →ₗ[ℝ] ℝ, f e = 0 ∧
      (∀ x ∈ D, 0 < f₀ x → 0 < f x) ∧
      (∀ x ∈ D, f x = 0 ↔ x ∈ Submodule.span ℝ ({e} : Set E)) := by
  classical
  let W : Submodule ℝ E := Submodule.span ℝ ({e} : Set E)
  let T : Finset E := D.filter (fun x => x ∉ W)
  have hv : ∀ x : T, W.mkQ (x : E) ≠ 0 := by
    intro x hx
    have hmem : (x : E) ∈ W := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    exact (Finset.mem_filter.mp x.property).2 hmem
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun x : T => W.mkQ (x : E)) hv
  let q : E →ₗ[ℝ] ℝ := g.comp W.mkQ
  have hqe : q e = 0 := by
    change g (W.mkQ e) = 0
    have heW : e ∈ W := Submodule.subset_span (by simp)
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr heW, map_zero]
  have hq : ∀ x ∈ D, x ∉ W → q x ≠ 0 := by
    intro x hx hxW
    exact hg ⟨x, Finset.mem_filter.mpr ⟨hx, hxW⟩⟩
  let radius : Option E → ℝ := fun x => match x with
    | none => 1
    | some x => if f₀ x = 0 then 1 else |f₀ x| / (|q x| + 1)
  let U : Finset (Option E) := insert none (D.image some)
  have hr : ∀ x ∈ U, 0 < radius x := by
    intro x _
    cases x with
    | none => norm_num [radius]
    | some x =>
      dsimp [radius]
      split_ifs with hx
      · norm_num
      · exact div_pos (abs_pos.mpr hx) (by positivity)
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image U radius ⟨none, by simp [U]⟩
  let ε : ℝ := radius x₀ / 2
  have hε : 0 < ε := div_pos (hr x₀ hx₀) (by norm_num)
  have hsmall : ∀ x ∈ D, f₀ x ≠ 0 → |ε * q x| < |f₀ x| := by
    intro x hx hne
    have hle := hmin (some x) (by simp [U, hx])
    have hrad : radius (some x) = |f₀ x| / (|q x| + 1) := by simp [radius, hne]
    rw [hrad] at hle
    have hepslt : ε < |f₀ x| / (|q x| + 1) := by
      dsimp [ε]
      linarith [hr x₀ hx₀]
    have hp : ε * (|q x| + 1) < |f₀ x| :=
      (lt_div_iff₀ (by positivity : 0 < |q x| + 1)).mp hepslt
    rw [abs_mul, abs_of_pos hε]
    nlinarith
  let f : E →ₗ[ℝ] ℝ := f₀ + ε • q
  have hfe : f e = 0 := by simp [f, h₀, hqe]
  have hpos : ∀ x ∈ D, 0 < f₀ x → 0 < f x := by
    intro x hx hfx
    have hl := (abs_lt.mp (hsmall x hx (ne_of_gt hfx))).1
    rw [abs_of_pos hfx] at hl
    change 0 < f₀ x + ε * q x
    linarith
  refine ⟨f, hfe, hpos, ?_⟩
  intro x hx
  constructor
  · intro hfx
    by_contra hxW
    by_cases hx₀ : f₀ x = 0
    · have heq : ε * q x = 0 := by simpa [f, hx₀, smul_eq_mul] using hfx
      exact (mul_ne_zero (ne_of_gt hε) (hq x hx hxW)) heq
    · have habs := hsmall x hx hx₀
      have heq : ε * q x = -f₀ x := by
        change f₀ x + ε * q x = 0 at hfx
        linarith
      rw [heq, abs_neg] at habs
      exact (lt_irrefl _) habs
  · exact annihilates_span e f hfe

/-- An explicit linear coordinate along a nonzero edge direction. -/
private lemma exists_edge_coordinate (e : E) (he : e ≠ 0) :
    ∃ τ : E →ₗ[ℝ] ℝ, τ e = 1 := by
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) (fun _ : Unit => e) (fun _ => he)
  refine ⟨(f e)⁻¹ • f, ?_⟩
  change (f e)⁻¹ * f e = 1
  exact inv_mul_cancel₀ (hf ())

/-- If two points differ along e, the normalized edge coordinate recovers the
actual scalar, not merely a direction-class label. -/
private lemma displacement_eq_coordinate (e : E) (τ : E →ₗ[ℝ] ℝ) (hτ : τ e = 1)
    (x y : E) (h : x - y ∈ Submodule.span ℝ ({e} : Set E)) :
    x = y + (τ x - τ y) • e := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
  have hval := congrArg τ ht
  simp only [map_smul, map_sub, smul_eq_mul, hτ, mul_one] at hval
  have heq : (τ x - τ y) • e = x - y := by rw [← hval]; exact ht
  rw [heq]
  abel

private lemma active_scalar {a c x y β : ℝ}
    (ha : 0<a) (hc : 0≤c) (hac : a+c=1)
    (hx : x≤β) (hy : y≤β) (he : a*x+c*y=β) : x=β := by
  by_contra hn
  have hlt : x<β := lt_of_le_of_ne hx hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hy hc
  have hscale : a*β+c*β=β := by rw [←add_mul,hac,one_mul]
  linarith

/-- Adapted from the already verified Minkowski support-slice core. -/
private theorem support_slice_extreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (hbound : ∀ x ∈ P, f x≤β) : IsExtreme ℝ P {x | x ∈ P ∧ f x = β} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp, ?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  have he := congrArg f hcomb
  simp only [map_add,map_smul,smul_eq_mul] at he
  exact active_scalar ha hc.le hac (hbound p hp) (hbound q hq) (he.trans hz.2)

private theorem convexHull_support_contained (S F : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (hF : Convex ℝ F)
    (hS : ∀ x ∈ S, f x≤β ∧ (f x=β → x∈F)) :
    ∀ x ∈ convexHull ℝ S, f x≤β ∧ (f x=β → x∈F) := by
  let good : Set E := {x | f x≤β ∧ (f x=β → x∈F)}
  have hgood : Convex ℝ good := by
    intro x hx y hy a c ha hc hac
    have he : f (a • x+c • y)=a*f x+c*f y := by simp
    have h₁ := mul_le_mul_of_nonneg_left hx.1 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hc
    refine ⟨?_, ?_⟩
    · rw [he]
      calc
        a*f x+c*f y ≤ a*β+c*β := add_le_add h₁ h₂
        _ = β := by rw [←add_mul,hac,one_mul]
    · intro ht
      by_cases ha0 : a=0
      · have hc1 : c=1 := by linarith
        simpa [ha0,hc1] using hy.2 (by simpa [ha0,hc1] using ht)
      by_cases hc0 : c=0
      · have ha1 : a=1 := by linarith
        simpa [hc0,ha1] using hx.2 (by simpa [hc0,ha1] using ht)
      have hapos : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hcpos : 0<c := lt_of_le_of_ne hc (Ne.symm hc0)
      have htop : a*f x+c*f y=β := he.symm.trans ht
      have hxeq := active_scalar hapos hc hac hx.1 hy.1 htop
      have hyeq := active_scalar hcpos ha (by linarith) hy.1 hx.1 (by nlinarith)
      exact hF (hx.2 hxeq) (hy.2 hyeq) ha hc hac
  exact convexHull_min (fun x hx => hS x hx) hgood

private theorem hull_slice_segment (S : Finset E)
    (f : E →ₗ[ℝ] ℝ) (a b : E)
    (ha : a∈S) (hb : b∈S) (hfb : f b=f a)
    (hbound : ∀ x∈S, f x≤f a)
    (hmax : ∀ x∈S, f x=f a → x∈segment ℝ a b) :
    {x | x ∈ convexHull ℝ (S : Set E) ∧ f x = f a} = segment ℝ a b := by
  have h := convexHull_support_contained (S : Set E) (segment ℝ a b) f (f a)
    (convex_segment a b) (fun x hx => ⟨hbound x hx,hmax x hx⟩)
  apply Set.Subset.antisymm
  · intro x hx
    exact (h x hx.1).2 hx.2
  · intro x hx
    obtain ⟨r,s,hr,hs,hrs,hcomb⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [←hcomb]
      exact (convex_convexHull ℝ (S : Set E)) (subset_convexHull ℝ (S : Set E) ha)
        (subset_convexHull ℝ (S : Set E) hb) hr hs hrs
    · rw [←hcomb]
      simp only [map_add,map_smul,smul_eq_mul,hfb]
      rw [←add_mul,hrs,one_mul]

private lemma interval_segment (a e : E) (η t : ℝ)
    (hη : 0 ≤ η) (ht : 0 ≤ t) (htη : t ≤ η) :
    a + t • e ∈ segment ℝ a (a + η • e) := by
  by_cases hz : η = 0
  · have ht0 : t = 0 := by linarith
    simp [hz, ht0]
  · have hp : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
    have hs : t / η ≤ 1 := (div_le_one hp).mpr htη
    have hm : (t / η) * η = t := div_mul_cancel₀ t hz
    refine ⟨1-t/η, t/η, by linarith, div_nonneg ht hη, by ring, ?_⟩
    simp only [smul_add, smul_smul, hm]
    module

/-- Generic ties force a whole finite-hull support face to be a parallel
segment. Endpoints and their nonnegative length are constructed by finite extrema. -/
theorem finite_parallel_support (S : Finset E) (hS : S.Nonempty)
    (e : E) (τ f : E →ₗ[ℝ] ℝ) (hτ : τ e = 1)
    (hties : ∀ x∈S, ∀ y∈S, f x=f y →
      x-y ∈ Submodule.span ℝ ({e} : Set E)) :
    ∃ a∈S, ∃ b∈S, ∃ η : ℝ, 0 ≤ η ∧ b=a+η • e ∧
      (∀ x∈S, f x ≤ f a) ∧
      {x | x ∈ convexHull ℝ (S : Set E) ∧ f x = f a} = segment ℝ a b := by
  classical
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S f hS
  let T := S.filter (fun x => f x = f p)
  have hT : T.Nonempty := ⟨p, by simp [T, hp]⟩
  obtain ⟨a, ha, hminτ⟩ := Finset.exists_min_image T τ hT
  obtain ⟨b, hb, hmaxτ⟩ := Finset.exists_max_image T τ hT
  have haS := (Finset.mem_filter.mp ha).1
  have hbS := (Finset.mem_filter.mp hb).1
  have haf : f a = f p := (Finset.mem_filter.mp ha).2
  have hbf : f b = f p := (Finset.mem_filter.mp hb).2
  let η := τ b - τ a
  have hη : 0 ≤ η := sub_nonneg.mpr (hminτ b hb)
  have hba : b = a + η • e :=
    displacement_eq_coordinate e τ hτ b a (hties b hbS a haS (hbf.trans haf.symm))
  have hfbound : ∀ x∈S, f x ≤ f a := by
    intro x hx
    rw [haf]
    exact hmax x hx
  refine ⟨a, haS, b, hbS, η, hη, hba, hfbound, ?_⟩
  apply hull_slice_segment S f a b haS hbS (hbf.trans haf.symm) hfbound
  intro x hx hfx
  have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hfx.trans haf⟩
  have hxa := displacement_eq_coordinate e τ hτ x a (hties x hx a haS hfx)
  rw [hxa, hba]
  apply interval_segment a e η (τ x - τ a) hη
  · exact sub_nonneg.mpr (hminτ x hxT)
  · dsimp [η]
    linarith [hmaxτ x hxT]

def sumHull (m : ℕ) (S : Fin m → Finset E) : Set E :=
  {z | ∃ x : Fin m → E, (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}

/-- Assemble the already established full component slices. This reuses the
finite supporting-face argument, not a normal-fan or graph-lifting oracle. -/
private theorem sum_parallel_slices (m : ℕ) (S : Fin m → Finset E)
    (f : E →ₗ[ℝ] ℝ) (e : E) (hfe : f e = 0)
    (a b : Fin m → E) (η : Fin m → ℝ)
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ S i)
    (hη : ∀ i, 0 ≤ η i) (hba : ∀ i, b i = a i + η i • e)
    (hbound : ∀ i, ∀ x ∈ S i, f x ≤ f (a i))
    (hface : ∀ i, {x | x ∈ convexHull ℝ (S i : Set E) ∧ f x = f (a i)} =
      segment ℝ (a i) (b i)) :
    (∀ z ∈ sumHull m S, f z ≤ f (∑ i, a i)) ∧
      {z | z ∈ sumHull m S ∧ f z = f (∑ i, a i)} =
        segment ℝ (∑ i, a i) (∑ i, b i) := by
  classical
  have hH : ∀ i, ∀ x ∈ convexHull ℝ (S i : Set E), f x ≤ f (a i) := by
    intro i x hx
    exact (convexHull_support_contained (S i : Set E) Set.univ f (f (a i))
      convex_univ (fun z hz => ⟨hbound i z hz, fun _ => Set.mem_univ _⟩) x hx).1
  have hsumB : (∑ i, b i) = (∑ i, a i) + (∑ i, η i) • e := by
    simp only [hba, Finset.sum_add_distrib, Finset.sum_smul]
  have hmax : ∀ z ∈ sumHull m S, f z ≤ f (∑ i, a i) := by
    rintro z ⟨x, hx, rfl⟩
    simp only [map_sum]
    exact Finset.sum_le_sum (fun i _ => hH i (x i) (hx i))
  refine ⟨hmax, Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨⟨x, hx, hxz⟩, hz⟩
    have htop : ∀ i, f (x i) = f (a i) := by
      intro i
      by_contra hn
      have hlt : (∑ j, f (x j)) < ∑ j, f (a j) :=
        Finset.sum_lt_sum (fun j _ => hH j (x j) (hx j))
          ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hH i (x i) (hx i)) hn⟩
      have heq : (∑ j, f (x j)) = ∑ j, f (a j) := by
        rw [← map_sum, hxz, hz, map_sum]
      linarith
    have hseg : ∀ i, x i ∈ segment ℝ (a i) (b i) := by
      intro i
      rw [← hface i]
      exact ⟨hx i, htop i⟩
    have hparam : ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ η i ∧ x i = a i + t • e := by
      intro i
      obtain ⟨r,s,hr,hs,hrs,hcomb⟩ := hseg i
      refine ⟨s * η i, mul_nonneg hs (hη i), ?_, ?_⟩
      · have hs1 : s ≤ 1 := by linarith
        simpa using mul_le_mul_of_nonneg_right hs1 (hη i)
      · rw [← hcomb, hba i]
        calc
          r • a i + s • (a i + η i • e) = (r+s) • a i + (s*η i) • e := by module
          _ = a i + (s*η i) • e := by rw [hrs, one_smul]
    choose t ht0 htη hxt using hparam
    have hzline : z = (∑ i, a i) + (∑ i, t i) • e := by
      rw [← hxz]
      simp only [hxt, Finset.sum_add_distrib, Finset.sum_smul]
    rw [hzline, hsumB]
    exact interval_segment _ e _ _
      (Finset.sum_nonneg (fun i _ => hη i))
      (Finset.sum_nonneg (fun i _ => ht0 i))
      (Finset.sum_le_sum (fun i _ => htη i))
  · rintro z ⟨r,s,hr,hs,hrs,hcomb⟩
    have hfab : f (∑ i, b i) = f (∑ i, a i) := by
      rw [hsumB, map_add, map_smul, hfe, smul_zero, add_zero]
    refine ⟨?_, ?_⟩
    · refine ⟨fun i => r • a i + s • b i, ?_, ?_⟩
      · intro i
        exact (convex_convexHull ℝ (S i : Set E))
          (subset_convexHull ℝ (S i : Set E) (ha i))
          (subset_convexHull ℝ (S i : Set E) (hb i)) hr hs hrs
      · simpa only [Finset.sum_add_distrib, ← Finset.smul_sum] using hcomb
    · rw [← hcomb, map_add, map_smul, map_smul, hfab]
      simp only [smul_eq_mul]
      rw [← add_mul, hrs, one_mul]

/-- Actual edge-surjectivity for an explicitly exposed finite-hull core edge.
The new objective and every summand's whole exposed segment are derived. -/
theorem exposed_core_edge_lift
    (m : ℕ) (c : Fin m) (S : Fin m → Finset E) (hS : ∀ i, (S i).Nonempty)
    (u v : E) (hu : u ∈ S c) (hv : v ∈ S c) (huv : u ≠ v)
    (f₀ : E →ₗ[ℝ] ℝ) (h₀ : f₀ v = f₀ u)
    (hbound₀ : ∀ x ∈ S c, f₀ x ≤ f₀ u)
    (hmax₀ : ∀ x ∈ S c, f₀ x = f₀ u → x ∈ segment ℝ u v) :
    ∃ (f : E →ₗ[ℝ] ℝ) (a b : Fin m → E) (η : Fin m → ℝ),
      f (v-u) = 0 ∧ a c = u ∧ b c = v ∧ η c = 1 ∧
      (∀ i, a i ∈ S i ∧ b i ∈ S i ∧ 0 ≤ η i ∧ b i = a i + η i • (v-u) ∧
        (∀ x ∈ S i, f x ≤ f (a i)) ∧
        {x | x ∈ convexHull ℝ (S i : Set E) ∧ f x = f (a i)} =
          segment ℝ (a i) (b i)) ∧
      (∑ i, a i) ≠ (∑ i, b i) ∧
      (∀ z ∈ sumHull m S, f z ≤ f (∑ i, a i)) ∧
      {z | z ∈ sumHull m S ∧ f z = f (∑ i, a i)} =
        segment ℝ (∑ i, a i) (∑ i, b i) ∧
      IsExtreme ℝ (sumHull m S) (segment ℝ (∑ i, a i) (∑ i, b i)) := by
  classical
  let e := v-u
  have he : e ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h₀e : f₀ e = 0 := by simp [e, map_sub, h₀]
  let D : Finset E := Finset.univ.biUnion (fun i : Fin m =>
    (S i ×ˢ S i).image (fun p => p.1-p.2))
  have hD : ∀ i, ∀ x∈S i, ∀ y∈S i, x-y ∈ D := by
    intro i x hx y hy
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩⟩
  obtain ⟨f,hfe,hpos,htie⟩ := generic_edge_objective e D f₀ h₀e
  obtain ⟨τ,hτ⟩ := exists_edge_coordinate e he
  have ht : ∀ i, ∀ x∈S i, ∀ y∈S i, f x=f y →
      x-y ∈ Submodule.span ℝ ({e} : Set E) := by
    intro i x hx y hy hxy
    apply (htie (x-y) (hD i x hx y hy)).mp
    simp [map_sub, hxy]
  have hfuv : f v = f u := by
    have hh : f v - f u = 0 := by simpa [e, map_sub] using hfe
    exact sub_eq_zero.mp hh
  have hfbound : ∀ x∈S c, f x ≤ f u := by
    intro x hx
    by_cases hx₀ : f₀ x=f₀ u
    · have hseg := hmax₀ x hx hx₀
      obtain ⟨r,s,hr,hs,hrs,hcomb⟩ := hseg
      have heq : f x = f u := by
        rw [← hcomb, map_add, map_smul, map_smul, hfuv]
        simp only [smul_eq_mul]
        rw [← add_mul, hrs, one_mul]
      exact heq.le
    · have hlt : f₀ x < f₀ u := lt_of_le_of_ne (hbound₀ x hx) hx₀
      have hp := hpos (u-x) (hD c u hu x hx) (by simpa [map_sub] using sub_pos.mpr hlt)
      have hh : 0 < f u-f x := by simpa [map_sub] using hp
      linarith
  have hfmax : ∀ x∈S c, f x=f u → x∈segment ℝ u v := by
    intro x hx hxu
    have hpar := ht c x hx u hu hxu
    have hz := annihilates_span e f₀ h₀e hpar
    have hx₀ : f₀ x=f₀ u := sub_eq_zero.mp (by simpa [map_sub] using hz)
    exact hmax₀ x hx hx₀
  have hcore := hull_slice_segment (S c) f u v hu hv hfuv hfbound hfmax
  have hex : ∀ i : Fin m, ∃ a∈S i, ∃ b∈S i, ∃ η : ℝ,
      0 ≤ η ∧ b=a+η • e ∧ (∀ x∈S i, f x≤f a) ∧
      {x | x∈convexHull ℝ (S i : Set E) ∧ f x=f a}=segment ℝ a b := by
    intro i
    exact finite_parallel_support (S i) (hS i) e τ f hτ (ht i)
  choose a₀ ha₀ b₀ hb₀ η₀ hη₀ hba₀ hbound hface using hex
  let a : Fin m → E := fun i => if i=c then u else a₀ i
  let b : Fin m → E := fun i => if i=c then v else b₀ i
  let η : Fin m → ℝ := fun i => if i=c then 1 else η₀ i
  have hac : a c=u := by simp [a]
  have hbc : b c=v := by simp [b]
  have hηc : η c=1 := by simp [η]
  have hall : ∀ i, a i∈S i ∧ b i∈S i ∧ 0≤η i ∧ b i=a i+η i • e ∧
      (∀ x∈S i, f x≤f (a i)) ∧
      {x | x∈convexHull ℝ (S i : Set E) ∧ f x=f (a i)}=segment ℝ (a i) (b i) := by
    intro i
    by_cases hi : i=c
    · subst i
      simp only [hac, hbc, hηc]
      exact ⟨hu,hv,by norm_num,by simp only [e, one_smul]; abel,hfbound,hcore⟩
    · simpa only [a,b,η,if_neg hi] using
        And.intro (ha₀ i) ⟨hb₀ i,hη₀ i,hba₀ i,hbound i,hface i⟩
  have hsum := sum_parallel_slices m S f e hfe a b η
    (fun i => (hall i).1) (fun i => (hall i).2.1)
    (fun i => (hall i).2.2.1) (fun i => (hall i).2.2.2.1)
    (fun i => (hall i).2.2.2.2.1) (fun i => (hall i).2.2.2.2.2)
  have hηsum : 1 ≤ ∑ i, η i := by
    have hh := Finset.single_le_sum (fun i _ => (hall i).2.2.1) (Finset.mem_univ c)
    simpa only [hηc] using hh
  have hsumB : (∑ i, b i) = (∑ i, a i)+(∑ i,η i) • e := by
    have hball : ∀ i, b i = a i + η i • e := fun i => (hall i).2.2.2.1
    simp only [hball, Finset.sum_add_distrib, Finset.sum_smul]
  have hne : (∑ i,a i) ≠ (∑ i,b i) := by
    intro heq
    rw [hsumB] at heq
    have hh := congrArg τ heq
    simp only [map_add, map_smul, smul_eq_mul, hτ, mul_one] at hh
    linarith
  refine ⟨f,a,b,η,hfe,hac,hbc,hηc,hall,hne,hsum.1,hsum.2,?_⟩
  rw [← hsum.2]
  exact support_slice_extreme (sumHull m S) f (f (∑ i,a i)) hsum.1

end HirschEdgeLift

/-- A finite-hull core edge has an exposed edge bridge in every finite Minkowski
sum. The objective, factor endpoints, lengths, and full slices are produced. -/
theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (c : Fin m) (S : Fin m → Finset E) (hS : ∀ i, (S i).Nonempty)
    (u v : E) (hu : u ∈ S c) (hv : v ∈ S c) (huv : u ≠ v)
    (f₀ : E →ₗ[ℝ] ℝ) (h₀ : f₀ v = f₀ u)
    (hbound₀ : ∀ x ∈ S c, f₀ x ≤ f₀ u)
    (hmax₀ : ∀ x ∈ S c, f₀ x = f₀ u → x ∈ segment ℝ u v) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    ∃ (f : E →ₗ[ℝ] ℝ) (a b : Fin m → E) (η : Fin m → ℝ),
      f (v-u) = 0 ∧ a c = u ∧ b c = v ∧ η c = 1 ∧
      (∀ i, a i ∈ S i ∧ b i ∈ S i ∧ 0 ≤ η i ∧ b i = a i + η i • (v-u) ∧
        (∀ x ∈ S i, f x ≤ f (a i)) ∧
        {x | x ∈ convexHull ℝ (S i : Set E) ∧ f x = f (a i)} =
          segment ℝ (a i) (b i)) ∧
      (∑ i, a i) ≠ (∑ i, b i) ∧
      (∀ z ∈ R, f z ≤ f (∑ i, a i)) ∧
      {z | z ∈ R ∧ f z = f (∑ i, a i)} = segment ℝ (∑ i, a i) (∑ i, b i) ∧
      IsExtreme ℝ R (segment ℝ (∑ i, a i) (∑ i, b i)) := by
  exact HirschEdgeLift.exposed_core_edge_lift m c S hS u v hu hv huv f₀ h₀ hbound₀ hmax₀

#print axioms HirschEdgeLift.generic_edge_objective
#print axioms HirschEdgeLift.finite_parallel_support
#print axioms HirschEdgeLift.exposed_core_edge_lift
#print axioms solution
