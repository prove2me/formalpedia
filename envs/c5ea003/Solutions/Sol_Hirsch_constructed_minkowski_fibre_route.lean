-- Prove2me | solution 1 for Hirsch.constructed_minkowski_fibre_route
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T04:34:34.850029+00:00
-- url     : https://prove2.me/submissions/24b8a2c2-6a38-4f35-89e7-6b85f4d0b87c

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section

namespace Hirsch
/-- Exact project adjacency, inlined in the public target. -/
def Adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u v : E) : Prop :=
  u ≠ v ∧ IsExtreme ℝ P (segment ℝ u v)
end Hirsch

open Set
open scoped BigOperators
set_option autoImplicit false
namespace HirschMinkowski
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

def supportFace (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ) : Set E :=
  {x | x ∈ P ∧ f x = β}
def sumSet (S : ι → Set E) : Set E :=
  {z | ∃ x : ι → E, (∀ i, x i ∈ S i) ∧ (∑ i, x i) = z}

private lemma active_scalar {a c x y β : ℝ}
    (ha : 0<a) (hc : 0≤c) (hac : a+c=1)
    (hx : x≤β) (hy : y≤β) (he : a*x+c*y=β) : x=β := by
  by_contra hn
  have hlt : x<β := lt_of_le_of_ne hx hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hy hc
  have hscale : a*β+c*β=β := by rw [←add_mul,hac,one_mul]
  linarith

theorem supportFace_isExtreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (hbound : ∀ x ∈ P, f x≤β) : IsExtreme ℝ P (supportFace P f β) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp, ?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  have he := congrArg f hcomb
  simp only [map_add,map_smul,smul_eq_mul] at he
  exact active_scalar ha hc.le hac (hbound p hp) (hbound q hq) (he.trans hz.2)

theorem adj_of_supportFace_eq_segment (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (x y : E) (hne : x≠y) (hbound : ∀ z ∈ P, f z≤β)
    (hface : supportFace P f β = segment ℝ x y) : Hirsch.Adj P x y := by
  refine ⟨hne, ?_⟩
  rw [←hface]
  exact supportFace_isExtreme P f β hbound

theorem convexHull_support_contained (S F : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
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

theorem convexHull_supportFace_eq_segment (S : Set E)
    (f : E →ₗ[ℝ] ℝ) (β : ℝ) (a b : E)
    (ha : a∈S) (hb : b∈S) (hfa : f a=β) (hfb : f b=β)
    (hbound : ∀ x∈S, f x≤β)
    (hmax : ∀ x∈S, f x=β → x∈segment ℝ a b) :
    supportFace (convexHull ℝ S) f β = segment ℝ a b := by
  have h := convexHull_support_contained S (segment ℝ a b) f β
    (convex_segment a b) (fun x hx => ⟨hbound x hx,hmax x hx⟩)
  apply Set.Subset.antisymm
  · intro x hx
    exact (h x hx.1).2 hx.2
  · intro x hx
    obtain ⟨r,s,hr,hs,hrs,hcomb⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [←hcomb]
      exact (convex_convexHull ℝ S) (subset_convexHull ℝ S ha)
        (subset_convexHull ℝ S hb) hr hs hrs
    · rw [←hcomb]
      simp only [map_add,map_smul,smul_eq_mul,hfa,hfb]
      rw [←add_mul,hrs,one_mul]

theorem sumSet_support_bound (S : ι → Set E) (f : E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (hbound : ∀ i, ∀ x∈S i, f x≤β i) :
    ∀ z∈sumSet S, f z≤∑ i, β i := by
  rintro z ⟨x,hx,rfl⟩
  rw [map_sum]
  exact Finset.sum_le_sum (fun i _ => hbound i (x i) (hx i))

theorem sumSet_supportFace (S : ι → Set E) (f : E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (hbound : ∀ i, ∀ x∈S i, f x≤β i) :
    supportFace (sumSet S) f (∑ i, β i) = sumSet (fun i => supportFace (S i) f (β i)) := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x,hx,hxz⟩,hz⟩
    refine ⟨x,?_,hxz⟩
    intro i
    refine ⟨hx i,?_⟩
    by_contra hn
    have hs : (∑ j, f (x j)) < ∑ j, β j :=
      Finset.sum_lt_sum (fun j _ => hbound j (x j) (hx j))
        ⟨i,Finset.mem_univ i,lt_of_le_of_ne (hbound i (x i) (hx i)) hn⟩
    have he : (∑ j, f (x j))=∑ j, β j := by rw [←map_sum,hxz,hz]
    linarith
  · rintro z ⟨x,hx,rfl⟩
    refine ⟨⟨x,fun i => (hx i).1,rfl⟩,?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => (hx i).2)

def intervalLine (a g : E) (η : ℝ) : Set E :=
  {x | ∃ t : ℝ, 0≤t ∧ t≤η ∧ x=a+t • g}

theorem sumSet_intervalLine (a : ι → E) (g : E) (η : ι → ℝ)
    (hη : ∀ i, 0≤η i) :
    sumSet (fun i => intervalLine (a i) g (η i)) =
      intervalLine (∑ i,a i) g (∑ i,η i) := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    choose t ht0 htη hxt using hx
    refine ⟨∑ i,t i,Finset.sum_nonneg (fun i _ => ht0 i),
      Finset.sum_le_sum (fun i _ => htη i),?_⟩
    simp only [hxt,Finset.sum_add_distrib,Finset.sum_smul]
  · rintro z ⟨t,ht0,htη,rfl⟩
    by_cases hzero : (∑ i,η i)=0
    · have ht : t=0 := by linarith
      refine ⟨a,fun i => ⟨0,le_rfl,hη i,by simp⟩,?_⟩
      simp [ht]
    · have hpos : 0<∑ i,η i := lt_of_le_of_ne
        (Finset.sum_nonneg (fun i _ => hη i)) (Ne.symm hzero)
      let r : ℝ := t/(∑ i,η i)
      have hr0 : 0≤r := div_nonneg ht0 hpos.le
      have hr1 : r≤1 := (div_le_one hpos).mpr htη
      have hrt : r*(∑ i,η i)=t := div_mul_cancel₀ t hzero
      refine ⟨fun i => a i+(r*η i) • g,?_,?_⟩
      · intro i
        exact ⟨r*η i,mul_nonneg hr0 (hη i),
          by simpa using mul_le_mul_of_nonneg_right hr1 (hη i),rfl⟩
      · rw [Finset.sum_add_distrib]
        congr 1
        calc
          (∑ i, (r*η i) • g) = (∑ i, r*η i) • g := by rw [Finset.sum_smul]
          _ = (r*(∑ i,η i)) • g := by rw [Finset.mul_sum]
          _ = t • g := by rw [hrt]

lemma intervalLine_eq_segment (a g : E) (η : ℝ) (hη : 0≤η) :
    intervalLine a g η = segment ℝ a (a+η • g) := by
  apply Set.Subset.antisymm
  · rintro z ⟨t,ht0,htη,rfl⟩
    by_cases hzero : η=0
    · have ht : t=0 := by linarith
      simp [ht,hzero]
    · have hpos : 0<η := lt_of_le_of_ne hη (Ne.symm hzero)
      have hr0 : 0≤t/η := div_nonneg ht0 hη
      have hr1 : t/η≤1 := (div_le_one hpos).mpr htη
      have hrt : (t/η)*η=t := div_mul_cancel₀ t hzero
      refine ⟨1-t/η,t/η,by linarith,hr0,by ring,?_⟩
      simp only [smul_add,smul_smul,hrt]
      module
  · rintro z ⟨r,s,hr,hs,hrs,hcomb⟩
    refine ⟨s*η,mul_nonneg hs hη,?_,?_⟩
    · have hs1 : s≤1 := by linarith
      simpa using mul_le_mul_of_nonneg_right hs1 hη
    · rw [←hcomb]
      calc
        r • a+s • (a+η • g) = (r+s) • a+(s*η) • g := by module
        _ = a+(s*η) • g := by rw [hrs,one_smul]
end HirschMinkowski

open Set HirschMinkowski
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace HirschEnvelopeCrossing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private lemma displacement (e : E) (τ : E →ₗ[ℝ] ℝ) (hτ : τ e = 1)
    (x y : E) (h : x-y ∈ Submodule.span ℝ ({e} : Set E)) :
    x = y + (τ x-τ y) • e := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hval := congrArg τ ha
  simp only [map_smul, map_sub, smul_eq_mul, hτ, mul_one] at hval
  have heq : (τ x-τ y) • e = x-y := by rw [← hval]; exact ha
  rw [heq]
  abel

private lemma interval_member (p e : E) (η z : ℝ)
    (hη : 0 ≤ η) (hz : 0 ≤ z) (hzη : z ≤ η) :
    p + z • e ∈ segment ℝ p (p + η • e) := by
  rw [← intervalLine_eq_segment p e η hη]
  exact ⟨z, hz, hzη, rfl⟩

theorem crossing_support_segments
    (m : ℕ) (S : Fin m → Finset E) (p q : Fin m → E)
    (left wall right : E →ₗ[ℝ] ℝ) (e : E)
    (hle : left e < 0) (hre : 0 < right e)
    (hp : ∀ i, p i ∈ S i) (hq : ∀ i, q i ∈ S i)
    (hl : ∀ i, ∀ x∈S i, left x ≤ left (p i))
    (hr : ∀ i, ∀ x∈S i, right x ≤ right (q i))
    (hw : ∀ i, ∀ x∈S i, wall x ≤ wall (p i))
    (hwq : ∀ i, wall (q i) = wall (p i))
    (hparallel : ∀ i, ∀ x∈S i, wall x = wall (p i) →
      x-p i ∈ Submodule.span ℝ ({e} : Set E)) :
    ∃ η : Fin m → ℝ, (∀ i, 0 ≤ η i) ∧
      (∀ i, q i = p i + η i • e) ∧
      ∀ i, supportFace (convexHull ℝ (S i : Set E)) wall (wall (p i)) =
        intervalLine (p i) e (η i) := by
  classical
  let τ : E →ₗ[ℝ] ℝ := (left e)⁻¹ • left
  have hτ : τ e = 1 := by
    change (left e)⁻¹ * left e = 1
    exact inv_mul_cancel₀ (ne_of_lt hle)
  let η : Fin m → ℝ := fun i => τ (q i)-τ (p i)
  have hqe : ∀ i, q i = p i + η i • e := by
    intro i
    exact displacement e τ hτ _ _ (hparallel i (q i) (hq i) (hwq i))
  have hη : ∀ i, 0 ≤ η i := by
    intro i
    have hv := hl i (q i) (hq i)
    rw [hqe i, map_add, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hneg : η i < 0 := lt_of_not_ge hn
    have hpos := mul_pos_of_neg_of_neg hneg hle
    linarith
  refine ⟨η, hη, hqe, ?_⟩
  intro i
  rw [intervalLine_eq_segment (p i) e (η i) (hη i), ← hqe i]
  apply convexHull_supportFace_eq_segment (S i : Set E) wall (wall (p i))
    (p i) (q i) (hp i) (hq i) rfl (hwq i) (hw i)
  intro x hx hxw
  let z : ℝ := τ x-τ (p i)
  have hxe : x = p i + z • e :=
    displacement e τ hτ _ _ (hparallel i x hx hxw)
  have hz : 0 ≤ z := by
    have hv := hl i x hx
    rw [hxe, map_add, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hneg : z < 0 := lt_of_not_ge hn
    have hpos := mul_pos_of_neg_of_neg hneg hle
    linarith
  have hzη : z ≤ η i := by
    have hv := hr i x hx
    rw [hxe, hqe i, map_add, map_add, map_smul, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hlt : η i < z := lt_of_not_ge hn
    have hp := mul_lt_mul_of_pos_right hlt hre
    linarith
  rw [hxe, hqe i]
  exact interval_member (p i) e (η i) z (hη i) hz hzη

theorem affine_crossing_exposed_edge
    (m : ℕ) (S : Fin m → Finset E) (p q : Fin m → E)
    (f g : E →ₗ[ℝ] ℝ) (s u t : ℝ) (c : Fin m)
    (hp : ∀ i, p i ∈ S i) (hq : ∀ i, q i ∈ S i)
    (hpq : p c ≠ q c)
    (hleft : ∀ i, ∀ x∈S i, x ≠ p i →
      (f + s • g) x < (f + s • g) (p i))
    (hright : ∀ i, ∀ x∈S i, x ≠ q i →
      (f + t • g) x < (f + t • g) (q i))
    (hwall : ∀ i, ∀ x∈S i, (f + u • g) x ≤ (f + u • g) (p i))
    (hwallq : ∀ i, (f + u • g) (q i) = (f + u • g) (p i))
    (hties : ∀ i, ∀ x∈S i, ∀ y∈S i, x ≠ y →
      (f + u • g) x = (f + u • g) y →
      ∀ j, ∀ v∈S j, ∀ w∈S j,
        (f + u • g) v = (f + u • g) w →
        v-w ∈ Submodule.span ℝ ({x-y} : Set E)) :
    (∀ z ∈ sumSet (fun i => convexHull ℝ (S i : Set E)),
      (f + u • g) z ≤ (f + u • g) (∑ i, p i)) ∧
    supportFace (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (f + u • g) ((f + u • g) (∑ i, p i)) =
        segment ℝ (∑ i, p i) (∑ i, q i) ∧
    Hirsch.Adj (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (∑ i, p i) (∑ i, q i) := by
  classical
  let e : E := q c-p c
  have he : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hl : (f + s • g) e < 0 := by
    have h := hleft c (q c) (hq c) (Ne.symm hpq)
    change (f + s • g) (q c-p c) < 0
    rw [map_sub]
    exact sub_neg.mpr h
  have hr : 0 < (f + t • g) e := by
    have h := hright c (p c) (hp c) hpq
    change 0 < (f + t • g) (q c-p c)
    rw [map_sub]
    exact sub_pos.mpr h
  have hln : ∀ i, ∀ x∈S i, (f + s • g) x ≤ (f + s • g) (p i) := by
    intro i x hx
    by_cases heq : x = p i
    · exact le_of_eq (congrArg (f + s • g) heq)
    · exact (hleft i x hx heq).le
  have hrn : ∀ i, ∀ x∈S i, (f + t • g) x ≤ (f + t • g) (q i) := by
    intro i x hx
    by_cases heq : x = q i
    · exact le_of_eq (congrArg (f + t • g) heq)
    · exact (hright i x hx heq).le
  have hpar : ∀ i, ∀ x∈S i, (f + u • g) x = (f + u • g) (p i) →
      x-p i ∈ Submodule.span ℝ ({e} : Set E) := by
    intro i x hx hxe
    exact hties c (q c) (hq c) (p c) (hp c) (Ne.symm hpq) (hwallq c)
      i x hx (p i) (hp i) hxe
  obtain ⟨η, hη, hqe, hface⟩ := crossing_support_segments m S p q
    (f + s • g) (f + u • g) (f + t • g) e hl hr hp hq hln hrn hwall hwallq hpar
  have hηc : η c = 1 := by
    have h := hqe c
    have hv := congrArg (f + s • g) h
    have hel : (f + s • g) (q c)-(f + s • g) (p c) = (f + s • g) e := by
      exact ((f + s • g).map_sub (q c) (p c)).symm
    simp only [map_add, map_smul, smul_eq_mul] at hv
    have hm : (η c-1) * (f + s • g) e = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (ne_of_lt hl))
  have hsumpos : 0 < ∑ i, η i := by
    have hle := Finset.single_le_sum (fun i _ => hη i) (Finset.mem_univ c)
    rw [hηc] at hle
    linarith
  have hsum : (∑ i, q i) = (∑ i, p i)+(∑ i, η i) • e := by
    simp only [hqe, Finset.sum_add_distrib, Finset.sum_smul]
  have hne : (∑ i, p i) ≠ (∑ i, p i)+(∑ i, η i) • e := by
    intro h
    have hv := congrArg (f + s • g) h
    simp only [map_add, map_smul, smul_eq_mul] at hv
    have hneg := mul_neg_of_pos_of_neg hsumpos hl
    linarith
  have hb : ∀ i, ∀ x∈convexHull ℝ (S i : Set E),
      (f + u • g) x ≤ (f + u • g) (p i) := by
    intro i x hx
    exact (convexHull_support_contained (S i : Set E) Set.univ
      (f + u • g) ((f + u • g) (p i)) convex_univ
      (fun z hz => ⟨hwall i z hz, fun _ => Set.mem_univ _⟩) x hx).1
  have hglobal : ∀ z ∈ sumSet (fun i => convexHull ℝ (S i : Set E)),
      (f + u • g) z ≤ (f + u • g) (∑ i, p i) := by
    intro z hz
    simpa only [map_sum] using
      sumSet_support_bound (fun i => convexHull ℝ (S i : Set E))
        (f + u • g) (fun i => (f + u • g) (p i)) hb z hz
  have hglobalface : supportFace (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (f + u • g) ((f + u • g) (∑ i, p i)) =
        segment ℝ (∑ i, p i) (∑ i, q i) := by
    rw [map_sum, sumSet_supportFace _ _ _ hb]
    have hf : (fun i => supportFace (convexHull ℝ (S i : Set E))
        (f + u • g) ((f + u • g) (p i))) =
        (fun i => intervalLine (p i) e (η i)) := funext hface
    rw [hf, sumSet_intervalLine p e η hη, hsum]
    exact intervalLine_eq_segment _ _ _ (Finset.sum_nonneg (fun i _ => hη i))
  refine ⟨hglobal, hglobalface, ?_⟩
  apply adj_of_supportFace_eq_segment _ (f + u • g) _ _ _
    (by simpa only [hsum] using hne) hglobal hglobalface
end HirschEnvelopeCrossing


open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Hirsch.FiniteAffineChambers

/-- A strict sign change of an affine scalar has an interior zero. -/
lemma zero_of_sign_change (a b l r : ℝ) (hlr : l < r)
    (hl : a + l*b < 0) (hr : 0 < a + r*b) :
    ∃ t : ℝ, l < t ∧ t < r ∧ a + t*b = 0 := by
  have hb : 0 < b := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlr.le)
      (le_of_not_gt hn)
    nlinarith
  refine ⟨-a/b, (lt_div_iff₀ hb).mpr (by linarith),
    (div_lt_iff₀ hb).mpr (by linarith), ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  ring

/-- A negative value and absence of interior zeros give strict negativity on
an entire chamber and the correct weak inequalities at BOTH boundary points. -/
lemma chamber_sign (a b l r s : ℝ) (hls : l < s) (hsr : s < r)
    (hs : a + s*b < 0)
    (hzero : ∀ t : ℝ, l < t → t < r → a + t*b ≠ 0) :
    (∀ t : ℝ, l ≤ t → t ≤ r → a + t*b ≤ 0) ∧
    (∀ t : ℝ, l < t → t < r → a + t*b < 0) := by
  have hclosed : ∀ t : ℝ, l ≤ t → t ≤ r → a + t*b ≤ 0 := by
    intro t hlt htr
    by_contra hn
    have ht : 0 < a + t*b := lt_of_not_ge hn
    rcases lt_trichotomy s t with hst | he | hts
    · obtain ⟨u, hsu, hut, hu⟩ := zero_of_sign_change a b s t hst hs ht
      exact hzero u (hls.trans hsu) (hut.trans_le htr) hu
    · subst t
      linarith
    · obtain ⟨u, htu, hus, hu⟩ := zero_of_sign_change (-a) (-b) t s hts
        (by nlinarith) (by nlinarith)
      exact hzero u (hlt.trans_lt htu) (hus.trans hsr) (by nlinarith [hu])
  exact ⟨hclosed, fun t hlt htr =>
    lt_of_le_of_ne (hclosed t hlt.le htr.le) (hzero t hlt htr)⟩

/-- Construct a finite ordered chamber decomposition from the ACTUAL affine
scores. No root list, interval winners, or wall-maximizing oracle is supplied.
Injectivity at time zero rules out identical affine scores within a factor.
Unused comparisons may create stationary adjacent chambers. -/
theorem exists_chambers
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (cut : Fin (N+2) → ℝ)
      (pick : Fin (N+1) → (i : Fin m) → Fin (k i)),
      StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last (N+1)) = 1 ∧
      pick 0 = p0 ∧ pick (Fin.last N) = p1 ∧
      (∀ j i q, q ≠ pick j i → ∀ t : ℝ,
        cut j.castSucc < t → t < cut j.succ →
        a i q + t*b i q < a i (pick j i) + t*b i (pick j i)) ∧
      (∀ j i q, ∀ t : ℝ,
        cut j.castSucc ≤ t → t ≤ cut j.succ →
        a i q + t*b i q ≤ a i (pick j i) + t*b i (pick j i)) := by
  classical
  let roots : Finset ℝ := (Finset.univ : Finset (Fin m)).biUnion fun i =>
    (Finset.univ : Finset (Fin (k i))).biUnion fun p =>
      (Finset.univ : Finset (Fin (k i))).image fun q =>
        (a i q-a i p)/(b i p-b i q)
  let C : Finset ℝ := insert 0 (insert 1 (roots.filter (fun t => 0 < t ∧ t < 1)))
  have h0 : (0 : ℝ) ∈ C := by simp [C]
  have h1 : (1 : ℝ) ∈ C := by simp [C]
  have hC : ∀ t ∈ C, 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    simp only [C, Finset.mem_insert, Finset.mem_filter] at ht
    rcases ht with rfl | rfl | ⟨_, hl, hr⟩
    · norm_num
    · norm_num
    · exact ⟨hl.le, hr.le⟩
  have hcard : 2 ≤ C.card := by
    have hs : ({0, 1} : Finset ℝ) ⊆ C := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have hh := Finset.card_le_card hs
    norm_num at hh
    exact hh
  let N := C.card-2
  have hc : C.card = N+2 := by dsimp [N]; omega
  let cut : Fin (N+2) ↪o ℝ := C.orderEmbOfFin hc
  have hmem : ∀ j, cut j ∈ C := fun j => C.orderEmbOfFin_mem hc j
  have honto : ∀ t ∈ C, ∃ j, cut j = t := by
    intro t ht
    refine ⟨(C.orderIsoOfFin hc).symm ⟨t, ht⟩, ?_⟩
    exact congrArg Subtype.val ((C.orderIsoOfFin hc).apply_symm_apply ⟨t, ht⟩)
  have hz : cut 0 = 0 := by
    obtain ⟨j, hj⟩ := honto 0 h0
    have hh := cut.monotone (Fin.zero_le j)
    rw [hj] at hh
    exact le_antisymm hh (hC _ (hmem 0)).1
  have ho : cut (Fin.last (N+1)) = 1 := by
    obtain ⟨j, hj⟩ := honto 1 h1
    have hh := cut.monotone (Fin.le_last j)
    rw [hj] at hh
    exact le_antisymm (hC _ (hmem _)).2 hh
  have hgap : ∀ (j : Fin (N+1)) (t : ℝ),
      cut j.castSucc < t → t < cut j.succ → t ∉ C := by
    intro j t hl hr ht
    obtain ⟨v, hv⟩ := honto t ht
    have hlv : j.castSucc < v := cut.lt_iff_lt.mp (by simpa [hv] using hl)
    have hvr : v < j.succ := cut.lt_iff_lt.mp (by simpa [hv] using hr)
    have hv1 : j.val < v.val := hlv
    have hv2 : v.val < j.val+1 := hvr
    omega
  have htie : ∀ i p q, p ≠ q → ∀ t : ℝ, 0 < t → t < 1 →
      a i p+t*b i p = a i q+t*b i q → t ∈ C := by
    intro i p q hpq t ht0 ht1 he
    have hd : b i p-b i q ≠ 0 := by
      intro hh
      have hh' := sub_eq_zero.mp hh
      have haa : a i p = a i q := by nlinarith [he]
      exact hpq (ha i haa)
    have heq : (a i q-a i p)/(b i p-b i q) = t := by
      apply (div_eq_iff hd).mpr
      nlinarith [he]
    have hr : t ∈ roots := by
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
      exact ⟨p, Finset.mem_univ _, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩⟩
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr (Or.inr ⟨hr, ht0, ht1⟩)
  let sample : Fin (N+1) → ℝ := fun j => (cut j.castSucc+cut j.succ)/2
  have hs : ∀ j : Fin (N+1), cut j.castSucc < sample j ∧ sample j < cut j.succ := by
    intro j
    have hh : cut j.castSucc < cut j.succ := cut.strictMono (by
      show j.val < j.val+1
      omega)
    dsimp [sample]
    constructor <;> linarith
  have hpick : ∀ (j : Fin (N+1)) (i : Fin m), ∃ p : Fin (k i),
      ∀ q : Fin (k i), a i q+sample j*b i q ≤ a i p+sample j*b i p := by
    intro j i
    obtain ⟨p, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k i)))
      (fun q => a i q+sample j*b i q) ⟨p0 i, Finset.mem_univ _⟩
    exact ⟨p, fun q => hmax q (Finset.mem_univ _)⟩
  choose pick hmax using hpick
  have hsample : ∀ j i q, q ≠ pick j i →
      a i q+sample j*b i q < a i (pick j i)+sample j*b i (pick j i) := by
    intro j i q hq
    apply lt_of_le_of_ne (hmax j i q)
    intro he
    exact hgap j (sample j) (hs j).1 (hs j).2
      (htie i q (pick j i) hq (sample j)
        ((hC _ (hmem _)).1.trans_lt (hs j).1)
        ((hs j).2.trans_le (hC _ (hmem _)).2) he)
  have hsign : ∀ j i q, q ≠ pick j i →
      (∀ t : ℝ, cut j.castSucc ≤ t → t ≤ cut j.succ →
        a i q+t*b i q ≤ a i (pick j i)+t*b i (pick j i)) ∧
      (∀ t : ℝ, cut j.castSucc < t → t < cut j.succ →
        a i q+t*b i q < a i (pick j i)+t*b i (pick j i)) := by
    intro j i q hq
    have hn : ∀ t : ℝ, cut j.castSucc < t → t < cut j.succ →
        (a i q-a i (pick j i))+t*(b i q-b i (pick j i)) ≠ 0 := by
      intro t hl hr he
      apply hgap j t hl hr
      apply htie i q (pick j i) hq t
        ((hC _ (hmem _)).1.trans_lt hl) (hr.trans_le (hC _ (hmem _)).2)
      nlinarith [he]
    obtain ⟨hw, ht⟩ := chamber_sign (a i q-a i (pick j i))
      (b i q-b i (pick j i)) (cut j.castSucc) (cut j.succ) (sample j)
      (hs j).1 (hs j).2 (by have hh := hsample j i q hq; nlinarith) hn
    constructor
    · intro t hl hr
      have hh := hw t hl hr
      nlinarith
    · intro t hl hr
      have hh := ht t hl hr
      nlinarith
  have hweak : ∀ j i q, ∀ t : ℝ, cut j.castSucc ≤ t → t ≤ cut j.succ →
      a i q+t*b i q ≤ a i (pick j i)+t*b i (pick j i) := by
    intro j i q t hl hr
    by_cases he : q = pick j i
    · subst q
      exact le_rfl
    · exact (hsign j i q he).1 t hl hr
  have hfirst : pick 0 = p0 := by
    funext i
    by_contra he
    have hu := hp0 i (pick 0 i) he
    have hw := hweak 0 i (p0 i) 0 (by simpa using hz.le) (hC _ (hmem _)).1
    simp only [zero_mul, add_zero] at hw
    linarith
  have hlast : pick (Fin.last N) = p1 := by
    funext i
    by_contra he
    have hu := hp1 i (pick (Fin.last N) i) he
    have hw := hweak (Fin.last N) i (p1 i) 1 (hC _ (hmem _)).2
      (by simpa using ho.ge)
    simp only [one_mul] at hw
    linarith
  exact ⟨N, cut, pick, cut.strictMono, hz, ho, hfirst, hlast,
    fun j i q hq => (hsign j i q hq).2, hweak⟩

end Hirsch.FiniteAffineChambers

namespace Hirsch.FiniteAffineChambers

/-- Delete stationary states while retaining the increasing sample order,
pointwise properties, and every genuine transition relation. The ending sample
may move earlier; its state remains the requested endpoint. -/
lemma compress_sequence {α : Type*} (P : ℝ → α → Prop) (R : α → α → Prop)
    (n : ℕ) (x : ℕ → α) (t : ℕ → ℝ)
    (ht : ∀ j, j < n → t j < t (j+1))
    (hP : ∀ j, j ≤ n → P (t j) (x j))
    (hR : ∀ j, j < n → R (x j) (x (j+1))) :
    ∃ (l : ℕ) (y : ℕ → α) (s : ℕ → ℝ),
      l ≤ n ∧ y 0 = x 0 ∧ y l = x n ∧
      (∀ j, j < l → s j < s (j+1)) ∧
      (∀ j, j ≤ l → P (s j) (y j)) ∧
      (∀ j, j < l → R (y j) (y (j+1))) ∧
      (∀ j, j < l → y j ≠ y (j+1)) ∧
      (∀ j, j ≤ l → s j ≤ t n) := by
  classical
  induction n with
  | zero =>
    refine ⟨0, x, t, le_rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; omega
    · intro j hj
      have he : j = 0 := by omega
      subst j
      exact hP 0 le_rfl
    · intro j hj; omega
    · intro j hj; omega
    · intro j hj
      have he : j = 0 := by omega
      subst j
      exact le_rfl
  | succ n ih =>
    obtain ⟨l, y, s, hln, hy0, hyn, hs, hyP, hyR, hyne, hst⟩ :=
      ih (fun j hj => ht j (by omega))
        (fun j hj => hP j (by omega)) (fun j hj => hR j (by omega))
    have htn : t n < t (n+1) := ht n (by omega)
    by_cases he : x n = x (n+1)
    · refine ⟨l, y, s, by omega, hy0, hyn.trans he, hs, hyP, hyR, hyne, ?_⟩
      intro j hj
      exact (hst j hj).trans htn.le
    · let z : ℕ → α := fun j => if j ≤ l then y j else x (n+1)
      let u : ℕ → ℝ := fun j => if j ≤ l then s j else t (n+1)
      refine ⟨l+1, z, u, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [z] using hy0
      · simp [z]
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [u, hj0, hj1] using hs j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [u] using (hst l le_rfl).trans_lt htn
      · intro j hj
        by_cases hjl : j ≤ l
        · simpa [u, z, hjl] using hyP j hjl
        · simpa [u, z, hjl] using hP (n+1) le_rfl
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [z, hj0, hj1] using hyR j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [z, hyn] using hR n (by omega)
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [z, hj0, hj1] using hyne j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [z, hyn] using he
      · intro j hj
        by_cases hjl : j ≤ l
        · simpa [u, hjl] using (hst j hjl).trans htn.le
        · simp [u, hjl]

/-- The finite crossing itinerary is derived, including stationary compression.
Every retained sample has a unique winner. Neighboring winners have a common
wall at which BOTH are globally maximizing in every factor. -/
theorem exists_itinerary
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨n, cut, p, hc, hz, ho, hpz, hpo, hstrict, hweak⟩ :=
    exists_chambers m k a b p0 p1 ha hp0 hp1
  let mid : Fin (n+1) → ℝ := fun j => (cut j.castSucc+cut j.succ)/2
  have hmid : ∀ j : Fin (n+1), cut j.castSucc < mid j ∧ mid j < cut j.succ := by
    intro j
    have hh := hc (show j.castSucc < j.succ by show j.val < j.val+1; omega)
    dsimp [mid]
    constructor <;> linarith
  have hcut : ∀ j, 0 ≤ cut j ∧ cut j ≤ 1 := by
    intro j
    constructor
    · have hh := hc.monotone (Fin.zero_le j); simpa [hz] using hh
    · have hh := hc.monotone (Fin.le_last j); simpa [ho] using hh
  let x : ℕ → (i : Fin m) → Fin (k i) := fun j =>
    if hj : j < n+1 then p ⟨j, hj⟩ else p1
  let t : ℕ → ℝ := fun j => if hj : j < n+1 then mid ⟨j, hj⟩ else 1
  let P : ℝ → ((i : Fin m) → Fin (k i)) → Prop := fun s v =>
    0 < s ∧ s < 1 ∧ ∀ i q, q ≠ v i → a i q+s*b i q < a i (v i)+s*b i (v i)
  let R : ((i : Fin m) → Fin (k i)) → ((i : Fin m) → Fin (k i)) → Prop :=
    fun v w => ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      (∀ i q, a i q+u*b i q ≤ a i (v i)+u*b i (v i)) ∧
      (∀ i, a i (w i)+u*b i (w i) = a i (v i)+u*b i (v i))
  have ht : ∀ j, j < n → t j < t (j+1) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hj1 : j+1 < n+1 := by omega
    have hleft := (hmid ⟨j, hj0⟩).2
    have hright := (hmid ⟨j+1, hj1⟩).1
    have he : (⟨j, hj0⟩ : Fin (n+1)).succ = (⟨j+1, hj1⟩ : Fin (n+1)).castSucc := by
      apply Fin.ext
      rfl
    rw [he] at hleft
    simpa only [t, dif_pos hj0, dif_pos hj1] using hleft.trans hright
  have hP : ∀ j, j ≤ n → P (t j) (x j) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hm := hmid ⟨j, hj0⟩
    have h0 := (hcut (⟨j, hj0⟩ : Fin (n+1)).castSucc).1.trans_lt hm.1
    have h1 := hm.2.trans_le (hcut (⟨j, hj0⟩ : Fin (n+1)).succ).2
    have hh : P (mid ⟨j, hj0⟩) (p ⟨j, hj0⟩) :=
      ⟨h0, h1, fun i q hq => hstrict ⟨j, hj0⟩ i q hq _ hm.1 hm.2⟩
    simpa only [t, x, dif_pos hj0] using hh
  have hR : ∀ j, j < n → R (x j) (x (j+1)) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hj1 : j+1 < n+1 := by omega
    let l : Fin (n+1) := ⟨j, hj0⟩
    let r : Fin (n+1) := ⟨j+1, hj1⟩
    have he : l.succ = r.castSucc := by apply Fin.ext; rfl
    have hlr : cut l.castSucc ≤ cut l.succ := hc.monotone (by show j ≤ j+1; omega)
    have hrr : cut r.castSucc ≤ cut r.succ := hc.monotone (by show j+1 ≤ j+1+1; omega)
    have hleft : ∀ i q, a i q+cut l.succ*b i q ≤
        a i (p l i)+cut l.succ*b i (p l i) :=
      fun i q => hweak l i q _ hlr le_rfl
    have hright : ∀ i q, a i q+cut l.succ*b i q ≤
        a i (p r i)+cut l.succ*b i (p r i) := by
      intro i q
      rw [he]
      exact hweak r i q _ le_rfl hrr
    have hh : R (p l) (p r) := by
      refine ⟨cut l.succ, (hcut _).1, (hcut _).2, hleft, ?_⟩
      intro i
      exact le_antisymm (hleft i (p r i)) (hright i (p l i))
    simpa only [R, x, dif_pos hj0, dif_pos hj1, l, r] using hh
  obtain ⟨N, y, s, _, hy0, hyn, hs, hyP, hyR, hyne, _⟩ :=
    compress_sequence P R n x t ht hP hR
  have hx0 : x 0 = p0 := by simpa [x] using hpz
  have hxn : x n = p1 := by simpa [x] using hpo
  exact ⟨N, s, y, hy0.trans hx0, hyn.trans hxn, hs, hyP, hyne, hyR⟩

end Hirsch.FiniteAffineChambers

namespace Hirsch.FiniteAffineChambers

lemma root_between (a b s t u : ℝ) (hst : s < t)
    (hs : a+s*b < 0) (ht : 0 < a+t*b) (hu : a+u*b = 0) : s < u ∧ u < t := by
  obtain ⟨v, hsv, hvt, hv⟩ := zero_of_sign_change a b s t hst hs ht
  have hb : b ≠ 0 := by intro hb; simp [hb] at hs ht; linarith
  have he : (u-v)*b = 0 := by nlinarith [hu, hv]
  have huv : u = v := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hb)
  simpa [huv] using (show s < v ∧ v < t from ⟨hsv, hvt⟩)

/-- Chronological retained crossings: no stationary step remains, and each
common supporting wall lies strictly between its two retained samples. -/
theorem crossing_sequence
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, time j < u ∧ u < time (j+1) ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨N, time, pick, h0, h1, hinc, hmax, hne, hwall⟩ :=
    exists_itinerary m k a b p0 p1 ha hp0 hp1
  refine ⟨N, time, pick, h0, h1, hinc, hmax, hne, ?_⟩
  intro j hj
  obtain ⟨u, _, _, hw, he⟩ := hwall j hj
  have hc : ∃ i, pick j i ≠ pick (j+1) i := by
    by_contra hn
    push_neg at hn
    exact hne j hj (funext hn)
  obtain ⟨i, hi⟩ := hc
  have hs := (hmax j (by omega)).2.2 i (pick (j+1) i) (Ne.symm hi)
  have ht := (hmax (j+1) (by omega)).2.2 i (pick j i) hi
  have hh := root_between
    (a i (pick (j+1) i)-a i (pick j i))
    (b i (pick (j+1) i)-b i (pick j i))
    (time j) (time (j+1)) u (hinc j hj)
    (by nlinarith) (by nlinarith) (by have hh := he i; nlinarith)
  exact ⟨u, hh.1, hh.2, hw, he⟩

end Hirsch.FiniteAffineChambers

-- The following slope-count proof is reused from accepted #239.
-- Only its enclosing namespace and public declaration name are changed.
namespace Hirsch.FiniteAffineChambers.Count

private def slopeRank {V : Type*} [Fintype V] (b : V → ℝ) (q : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p => b p < b q)).card

private theorem slopeRank_lt_card {V : Type*} [Fintype V]
    (b : V → ℝ) (q : V) : slopeRank b q < Fintype.card V := by
  classical
  let s := Finset.univ.filter (fun p => b p < b q)
  have hsub : s ⊂ (Finset.univ : Finset V) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hq : q ∈ s := by rw [he]; exact Finset.mem_univ q
    have hlt : b q < b q := (Finset.mem_filter.mp hq).2
    exact (lt_irrefl _) hlt
  exact Finset.card_lt_card hsub

private theorem slopeRank_mono {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p ≤ b q) : slopeRank b p ≤ slopeRank b q := by
  classical
  apply Finset.card_le_card
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hv).2 h⟩

private theorem slopeRank_strict {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p < b q) : slopeRank b p < slopeRank b q := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hv).2 h⟩
  · intro he
    have hp : p ∈ Finset.univ.filter (fun v => b v < b q) := by simp [h]
    rw [← he] at hp
    exact (lt_irrefl _) (Finset.mem_filter.mp hp).2

private theorem changed_maximizer_slope {V : Type*}
    (a b : V → ℝ) (p q : V) (s t : ℝ) (hst : s < t)
    (hleft : a q + s*b q < a p + s*b p)
    (hright : a p + t*b p < a q + t*b q) : b p < b q := by
  by_contra hn
  have hb : b q ≤ b p := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hb)
  nlinarith

theorem switch_bound
    (r N : ℕ) (k : Fin r → ℕ)
    (a b : (i : Fin r) → Fin (k i) → ℝ)
    (pick : ℕ → (i : Fin r) → Fin (k i)) (time : ℕ → ℝ)
    (hinc : ∀ j, j < N → time j < time (j+1))
    (hmax : ∀ j, j ≤ N → ∀ i q, q ≠ pick j i →
      a i q + time j*b i q < a i (pick j i) + time j*b i (pick j i))
    (hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i) :
    N ≤ ∑ i, (k i - 1) := by
  classical
  let rank : ℕ → Fin r → ℕ := fun j i => slopeRank (b i) (pick j i)
  have hstep : ∀ j, j < N → (∑ i, rank j i) < ∑ i, rank (j+1) i := by
    intro j hj
    have hslope : ∀ i, pick j i ≠ pick (j+1) i → b i (pick j i) < b i (pick (j+1) i) := by
      intro i hi
      exact changed_maximizer_slope (a i) (b i) (pick j i) (pick (j+1) i)
        (time j) (time (j+1)) (hinc j hj)
        (hmax j (by omega) i (pick (j+1) i) (Ne.symm hi))
        (hmax (j+1) (by omega) i (pick j i) hi)
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : pick j i = pick (j+1) i
      · simp only [rank, hi]
        exact le_rfl
      · exact slopeRank_mono (b i) _ _ (hslope i hi).le
    · obtain ⟨i, hi⟩ := hchange j hj
      exact ⟨i, Finset.mem_univ _, slopeRank_strict (b i) _ _ (hslope i hi)⟩
  have hgrow : ∀ j, j ≤ N → j ≤ ∑ i, rank j i := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnext := hstep j (by omega)
      omega
  have htop : (∑ i, rank N i) ≤ ∑ i, (k i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have h := slopeRank_lt_card (b i) (pick N i)
    simp only [Fintype.card_fin] at h
    change slopeRank (b i) (pick N i) ≤ k i - 1
    omega
  exact (hgrow N le_rfl).trans htop
end Hirsch.FiniteAffineChambers.Count

/-- Construct the bounded finite envelope itinerary, rather than assuming its
sample times, crossing list, unique interval winners or wall certificates. -/
theorem Hirsch.FiniteAffineChambers.bounded_crossing_sequence
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      N ≤ ∑ i, (k i-1) ∧ pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, time j < u ∧ u < time (j+1) ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨N, time, pick, h0, h1, hinc, hmax, hne, hwall⟩ :=
    Hirsch.FiniteAffineChambers.crossing_sequence m k a b p0 p1 ha hp0 hp1
  have hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i := by
    intro j hj
    by_contra hn
    push_neg at hn
    exact hne j hj (funext hn)
  have hb := Hirsch.FiniteAffineChambers.Count.switch_bound m N k a b pick time hinc
    (fun j hj => (hmax j hj).2.2) hchange
  exact ⟨N, time, pick, hb, h0, h1, hinc, hmax, hne, hwall⟩



open scoped BigOperators
set_option autoImplicit false
namespace HirschEnvelopeSequence

/-- Reindex the already verified #243 itinerary without changing its sequence,
count, endpoints or wall witnesses. The independent duplicate scalar proof was
withheld; this adapter uses the exact verified source of the other agent. -/
theorem exists_bounded_crossing_sequence
    (r : ℕ) (k : Fin r → ℕ)
    (a b : (i : Fin r) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin r) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q≠p0 i → a i q<a i (p0 i))
    (hp1 : ∀ i q, q≠p1 i → a i q+b i q<a i (p1 i)+b i (p1 i)) :
    ∃ N : ℕ, ∃ pick : ℕ → (i : Fin r) → Fin (k i), ∃ time wall : ℕ → ℝ,
      N ≤ ∑ i, (k i-1) ∧ pick 0=p0 ∧ pick N=p1 ∧
      (∀ j, j≤N → 0<time j ∧ time j<1) ∧
      (∀ j, j<N → time j<time (j+1)) ∧
      (∀ j, j≤N → ∀ i q, q≠pick j i →
        a i q+time j*b i q<a i (pick j i)+time j*b i (pick j i)) ∧
      ∀ j, j<N → time j<wall j ∧ wall j<time (j+1) ∧
        (∃ i, pick j i≠pick (j+1) i) ∧
        (∀ i q, a i q+wall j*b i q≤a i (pick j i)+wall j*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+wall j*b i (pick (j+1) i)=
          a i (pick j i)+wall j*b i (pick j i)) := by
  classical
  obtain ⟨N,time,pick,hN,h0,h1,hinc,hmax,hne,hwall⟩ :=
    Hirsch.FiniteAffineChambers.bounded_crossing_sequence r k a b p0 p1 ha hp0 hp1
  let wall : ℕ → ℝ := fun j => if hj:j<N then Classical.choose (hwall j hj) else 0
  refine ⟨N,pick,time,wall,hN,h0,h1,
    (fun j hj => ⟨(hmax j hj).1,(hmax j hj).2.1⟩),hinc,
    (fun j hj => (hmax j hj).2.2),?_⟩
  intro j hj
  have hw := Classical.choose_spec (hwall j hj)
  have hchange : ∃ i, pick j i≠pick (j+1) i := by
    by_contra h
    apply hne j hj
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  dsimp only [wall]
  rw [dif_pos hj]
  exact ⟨hw.1,hw.2.1,hchange,hw.2.2.1,hw.2.2.2⟩

end HirschEnvelopeSequence


open Set HirschMinkowski
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace HirschConstructedFibre
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- The constructed finite sequence, not supplied supporting faces, gives a
short route of actual exposed edges whenever simultaneous ties are parallel. -/
theorem route_of_generic_line (r : ℕ) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E)
    (f g : E →ₗ[ℝ] ℝ) (p0 p1 : (i : Fin r) → Fin (k i))
    (ha : ∀ i, Function.Injective (fun q => f (v i q)))
    (hp0 : ∀ i q, q≠p0 i → f (v i q)<f (v i (p0 i)))
    (hp1 : ∀ i q, q≠p1 i → (f+g) (v i q)<(f+g) (v i (p1 i)))
    (hties : ∀ u : ℝ, 0<u → u<1 →
      ∀ i p q, p≠q → (f+u • g) (v i p)=(f+u • g) (v i q) →
      ∀ j z w, (f+u • g) (v j z)=(f+u • g) (v j w) →
        v j z-v j w ∈ Submodule.span ℝ ({v i p-v i q} : Set E)) :
    let R := sumSet (fun i => convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E))
    ∃ N : ℕ, N≤∑ i, (k i-1) ∧ ∃ path : ℕ → E,
      path 0=∑ i, v i (p0 i) ∧ path N=∑ i, v i (p1 i) ∧
      (∀ j, j≤N → path j∈R) ∧
      ∀ j, j<N → ∃ u : ℝ, 0<u ∧ u<1 ∧
        (∀ z∈R, (f+u • g) z≤(f+u • g) (path j)) ∧
        supportFace R (f+u • g) ((f+u • g) (path j))=
          segment ℝ (path j) (path (j+1)) ∧ Hirsch.Adj R (path j) (path (j+1)) := by
  classical
  dsimp only
  let S : Fin r → Finset E := fun i => Finset.univ.image (v i)
  have hvinj : ∀ i, Function.Injective (v i) := by
    intro i p q he
    exact ha i (congrArg f he)
  obtain ⟨N,pick,time,wall,hN,h0,h1,ht01,hinc,hmax,hwall⟩ :=
    HirschEnvelopeSequence.exists_bounded_crossing_sequence r k
      (fun i q => f (v i q)) (fun i q => g (v i q)) p0 p1 ha hp0
      (by simpa only [LinearMap.add_apply] using hp1)
  let path : ℕ → E := fun j => ∑ i, v i (pick j i)
  refine ⟨N,hN,path,?_,?_,?_,?_⟩
  · simp only [path,h0]
  · simp only [path,h1]
  · intro j hj
    refine ⟨(fun i => v i (pick j i)),?_,rfl⟩
    intro i
    apply subset_convexHull ℝ
    exact Finset.mem_image.mpr ⟨pick j i,Finset.mem_univ _,rfl⟩
  · intro j hj
    obtain ⟨hl,hr,⟨c,hc⟩,hw,hwe⟩ := hwall j hj
    have hu0 : 0<wall j := (ht01 j (by omega)).1.trans hl
    have hu1 : wall j<1 := hr.trans (ht01 (j+1) (by omega)).2
    have hp : ∀ i, v i (pick j i)∈S i := fun i =>
      Finset.mem_image.mpr ⟨pick j i,Finset.mem_univ _,rfl⟩
    have hq : ∀ i, v i (pick (j+1) i)∈S i := fun i =>
      Finset.mem_image.mpr ⟨pick (j+1) i,Finset.mem_univ _,rfl⟩
    have hleft : ∀ i, ∀ x∈S i, x≠v i (pick j i) →
        (f+time j • g) x<(f+time j • g) (v i (pick j i)) := by
      intro i x hx hne
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
      have hqi : q≠pick j i := fun he => hne (congrArg (v i) he)
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
        hmax j (by omega) i q hqi
    have hright : ∀ i, ∀ x∈S i, x≠v i (pick (j+1) i) →
        (f+time (j+1) • g) x<(f+time (j+1) • g) (v i (pick (j+1) i)) := by
      intro i x hx hne
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
      have hqi : q≠pick (j+1) i := fun he => hne (congrArg (v i) he)
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
        hmax (j+1) (by omega) i q hqi
    have hwall' : ∀ i, ∀ x∈S i,
        (f+wall j • g) x≤(f+wall j • g) (v i (pick j i)) := by
      intro i x hx
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using hw i q
    have hwallq : ∀ i, (f+wall j • g) (v i (pick (j+1) i))=
        (f+wall j • g) (v i (pick j i)) := by
      intro i
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using hwe i
    have hparallel : ∀ i, ∀ x∈S i, ∀ y∈S i, x≠y →
        (f+wall j • g) x=(f+wall j • g) y →
        ∀ l, ∀ z∈S l, ∀ w∈S l,
          (f+wall j • g) z=(f+wall j • g) w →
          z-w∈Submodule.span ℝ ({x-y}:Set E) := by
      intro i x hx y hy hne he l z hz w hw hezw
      obtain ⟨px,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨py,_,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨pz,_,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨pw,_,rfl⟩ := Finset.mem_image.mp hw
      exact hties (wall j) hu0 hu1 i px py (fun h => hne (congrArg (v i) h)) he l pz pw hezw
    have h := HirschEnvelopeCrossing.affine_crossing_exposed_edge r S
      (fun i => v i (pick j i)) (fun i => v i (pick (j+1) i))
      f g (time j) (wall j) (time (j+1)) c hp hq
      (fun he => hc (hvinj c he)) hleft hright hwall' hwallq hparallel
    exact ⟨wall j,hu0,hu1,h.1,h.2.1,h.2.2⟩

end HirschConstructedFibre

namespace HirschConstructedFibre.Generic
private theorem finite_perturbation
    {I : Type*} [Fintype I] (a b : I → ℝ) :
    ∃ t : ℝ, 0 < t ∧
      (∀ i, a i < 0 → a i + t * b i < 0) ∧
      (∀ i, a i ≠ 0 ∨ b i ≠ 0 → a i + t * b i ≠ 0) := by
  classical
  let radius : Option I → ℝ := fun i => match i with
    | none => 1
    | some i => if a i = 0 then 1 else |a i| / (2 * (|b i| + 1))
  have hr : ∀ i, 0 < radius i := by
    intro i
    cases i with
    | none => norm_num [radius]
    | some i =>
      dsimp [radius]
      split_ifs with hi
      · norm_num
      · exact div_pos (abs_pos.mpr hi) (by positivity)
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Option I)) radius ⟨none, Finset.mem_univ _⟩
  let t := radius i₀
  have ht : 0 < t := hr i₀
  have hsmall : ∀ i, a i ≠ 0 → |t * b i| < |a i| := by
    intro i hi
    have hle : t ≤ |a i| / (2 * (|b i| + 1)) := by
      simpa only [radius, if_neg hi] using hmin (some i) (Finset.mem_univ _)
    have hprod : t * (2 * (|b i| + 1)) ≤ |a i| :=
      (le_div_iff₀ (by positivity)).mp hle
    rw [abs_mul, abs_of_pos ht]
    have hb : 0 ≤ |b i| := abs_nonneg _
    have hnon := mul_nonneg ht.le hb
    nlinarith
  refine ⟨t, ht, ?_, ?_⟩
  · intro i hi
    have h := hsmall i (ne_of_lt hi)
    rw [abs_of_neg hi] at h
    have hb := le_abs_self (t * b i)
    linarith
  · intro i hi
    by_cases ha : a i = 0
    · have hb : b i ≠ 0 := hi.resolve_left (not_not.mpr ha)
      simpa only [ha, zero_add] using mul_ne_zero (ne_of_gt ht) hb
    · intro he
      have hab : |t * b i| = |a i| := by
        have hneg : t * b i = -a i := by linarith
        rw [hneg, abs_neg]
      exact (ne_of_lt (hsmall i ha)) hab

private theorem avoiding_preserving_comparisons
    {E I J : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] [Fintype J]
    (f₀ : E →ₗ[ℝ] ℝ) (c : I → E) (v : J → E)
    (hc : ∀ i, f₀ (c i) < 0) (hv : ∀ j, v j ≠ 0) :
    ∃ f : E →ₗ[ℝ] ℝ,
      (∀ i, f (c i) < 0) ∧ (∀ j, f (v j) ≠ 0) := by
  classical
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) v hv
  let w : I ⊕ J → E := Sum.elim c v
  obtain ⟨t, ht, hneg, hne⟩ :=
    finite_perturbation (fun i => f₀ (w i)) (fun i => h (w i))
  refine ⟨f₀ + t • h, ?_, ?_⟩
  · intro i
    exact hneg (.inl i) (hc i)
  · intro j
    exact hne (.inr j) (Or.inr (hh j))

private theorem two_affine_zeros_force_determinant
    (a b c d t : ℝ) (ha : a ≠ 0)
    (hi : (1-t)*a+t*b=0) (hj : (1-t)*c+t*d=0) : a*d-c*b=0 := by
  have ht : t ≠ 0 := by
    intro ht
    have hz : a = 0 := by simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hi
    exact ha hz
  have he : t*(a*d-c*b)=0 := by
    linear_combination a*hj-c*hi
  exact (mul_eq_zero.mp he).resolve_left ht

/-- Any two nonempty finite strict endpoint cones have an objective segment
that never annihilates two linearly independent listed difference vectors.
Every endpoint comparison is preserved. No normal-fan genericity oracle,
full-dimensionality, or probabilistic assumption is supplied. -/
theorem generic_objectives
    {E A B I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype A] [Fintype B] [Fintype I]
    (f₀ g₀ : E →ₗ[ℝ] ℝ) (c₀ : A → E) (c₁ : B → E) (v : I → E)
    (hc₀ : ∀ a, f₀ (c₀ a) < 0)
    (hc₁ : ∀ b, g₀ (c₁ b) < 0)
    (hv : ∀ i, v i ≠ 0) :
    ∃ f g : E →ₗ[ℝ] ℝ,
      (∀ a, f (c₀ a) < 0) ∧
      (∀ b, g (c₁ b) < 0) ∧
      (∀ i, f (v i) ≠ 0) ∧
      (∀ i, g (v i) ≠ 0) ∧
      (∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
        f (v i)*g (v j)-f (v j)*g (v i) ≠ 0) ∧
      ∀ (t : ℝ) (i j : I),
        ((1-t)*f (v i)+t*g (v i)=0) →
        ((1-t)*f (v j)+t*g (v j)=0) →
        v j ∈ Submodule.span ℝ ({v i} : Set E) := by
  classical
  obtain ⟨f, hfc, hfv⟩ := avoiding_preserving_comparisons f₀ c₀ v hc₀ hv
  let Bad := {ij : I × I // v ij.2 ∉ Submodule.span ℝ ({v ij.1} : Set E)}
  let d : Bad → E := fun ij =>
    f (v ij.1.1) • v ij.1.2 - f (v ij.1.2) • v ij.1.1
  have hd : ∀ ij, d ij ≠ 0 := by
    intro ij hz
    have he : f (v ij.1.1) • v ij.1.2 = f (v ij.1.2) • v ij.1.1 :=
      sub_eq_zero.mp hz
    let W : Submodule ℝ E := Submodule.span ℝ ({v ij.1.1} : Set E)
    have hm : f (v ij.1.1) • v ij.1.2 ∈ W := by
      rw [he]
      exact W.smul_mem _ (Submodule.subset_span (by simp))
    exact ij.2 ((W.smul_mem_iff (hfv ij.1.1)).mp hm)
  let all : I ⊕ Bad → E := Sum.elim v d
  have hall : ∀ q, all q ≠ 0 := by
    intro q
    cases q with
    | inl i => exact hv i
    | inr ij => exact hd ij
  obtain ⟨g, hgc, hgv⟩ := avoiding_preserving_comparisons g₀ c₁ all hc₁ hall
  have hdet : ∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
      f (v i)*g (v j)-f (v j)*g (v i) ≠ 0 := by
    intro i j hij
    have hh := hgv (.inr ⟨(i,j),hij⟩)
    change g (f (v i) • v j - f (v j) • v i) ≠ 0 at hh
    simpa only [map_sub, map_smul, smul_eq_mul] using hh
  refine ⟨f, g, hfc, hgc, hfv, (fun i => hgv (.inl i)), hdet, ?_⟩
  intro t i j hi hj
  by_contra hij
  exact hdet i j hij (two_affine_zeros_force_determinant
    (f (v i)) (g (v i)) (f (v j)) (g (v j)) t (hfv i) hi hj)


end HirschConstructedFibre.Generic

namespace HirschConstructedFibre
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- A complete finite Minkowski fibre route is now CONSTRUCTED from the factor
points and exposed endpoint tuples. Genericity, event ordering, boundary
maximizers, compression, whole supporting segments and the additive count are
all derived. Factor presentations and exposed endpoints remain actual inputs. -/
theorem finite_sum_exposed_route_preserving
    {J : Type*} [Fintype J] (comparison : J → E)
    (r : ℕ) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E) (hinj : ∀ i, Function.Injective (v i))
    (p0 p1 : (i : Fin r) → Fin (k i)) (f0 g0 : E →ₗ[ℝ] ℝ)
    (hp0 : ∀ i q, q≠p0 i → f0 (v i q)<f0 (v i (p0 i)))
    (hp1 : ∀ i q, q≠p1 i → g0 (v i q)<g0 (v i (p1 i)))
    (hcomp0 : ∀ j, f0 (comparison j)<0)
    (hcomp1 : ∀ j, g0 (comparison j)<0) :
    let R := sumSet (fun i => convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E))
    ∃ N : ℕ, N≤∑ i, (k i-1) ∧ ∃ path : ℕ → E,
      path 0=∑ i, v i (p0 i) ∧ path N=∑ i, v i (p1 i) ∧
      (∀ j, j≤N → path j∈R) ∧
      ∀ j, j<N →
        (∃ h : E →ₗ[ℝ] ℝ, (∀ c, h (comparison c)<0) ∧
          (∀ z∈R, h z≤h (path j)) ∧
          supportFace R h (h (path j))=segment ℝ (path j) (path (j+1))) ∧
        Hirsch.Adj R (path j) (path (j+1)) := by
  classical
  dsimp only
  let D := {z : (i : Fin r) × (Fin (k i) × Fin (k i)) // z.2.1≠z.2.2}
  let C0 := {z : (i : Fin r) × Fin (k i) // z.2≠p0 z.1}
  let C1 := {z : (i : Fin r) × Fin (k i) // z.2≠p1 z.1}
  let delta : D → E := fun z => v z.1.1 z.1.2.1-v z.1.1 z.1.2.2
  let comp0 : C0 ⊕ J → E := Sum.elim
    (fun z => v z.1.1 z.1.2-v z.1.1 (p0 z.1.1)) comparison
  let comp1 : C1 ⊕ J → E := Sum.elim
    (fun z => v z.1.1 z.1.2-v z.1.1 (p1 z.1.1)) comparison
  have hc0 : ∀ z, f0 (comp0 z)<0 := by
    intro z
    cases z with
    | inl z =>
      change f0 (v z.1.1 z.1.2-v z.1.1 (p0 z.1.1))<0
      rw [map_sub]
      exact sub_neg.mpr (hp0 z.1.1 z.1.2 z.2)
    | inr j => exact hcomp0 j
  have hc1 : ∀ z, g0 (comp1 z)<0 := by
    intro z
    cases z with
    | inl z =>
      change g0 (v z.1.1 z.1.2-v z.1.1 (p1 z.1.1))<0
      rw [map_sub]
      exact sub_neg.mpr (hp1 z.1.1 z.1.2 z.2)
    | inr j => exact hcomp1 j
  have hd : ∀ z, delta z≠0 := by
    intro z
    exact sub_ne_zero.mpr (fun he => z.2 (hinj z.1.1 he))
  obtain ⟨f,g,hf,hg,hfd,hgd,hdet,ht⟩ :=
    Generic.generic_objectives f0 g0 comp0 comp1 delta hc0 hc1 hd
  have hfa : ∀ i, Function.Injective (fun q => f (v i q)) := by
    intro i p q he
    change f (v i p) = f (v i q) at he
    by_contra hpq
    have hn := hfd ⟨⟨i,(p,q)⟩,hpq⟩
    apply hn
    change f (v i p-v i q)=0
    rw [map_sub,he,sub_self]
  have hstart : ∀ i q, q≠p0 i → f (v i q)<f (v i (p0 i)) := by
    intro i q hq
    have h := hf (.inl ⟨⟨i,q⟩,hq⟩)
    change f (v i q-v i (p0 i))<0 at h
    rw [map_sub] at h
    exact sub_neg.mp h
  have hfinish : ∀ i q, q≠p1 i → (f+(g-f)) (v i q)<(f+(g-f)) (v i (p1 i)) := by
    intro i q hq
    have h := hg (.inl ⟨⟨i,q⟩,hq⟩)
    change g (v i q-v i (p1 i))<0 at h
    rw [map_sub] at h
    simp only [LinearMap.add_apply,LinearMap.sub_apply]
    linarith
  have hties : ∀ u : ℝ, 0<u → u<1 →
      ∀ i p q, p≠q → (f+u • (g-f)) (v i p)=(f+u • (g-f)) (v i q) →
      ∀ j z w, (f+u • (g-f)) (v j z)=(f+u • (g-f)) (v j w) →
        v j z-v j w∈Submodule.span ℝ ({v i p-v i q}:Set E) := by
    intro u _hu0 _hu1 i p q hpq he j z w hezw
    by_cases hzw : z=w
    · subst w
      simp only [sub_self,Submodule.zero_mem]
    · apply ht u ⟨⟨i,(p,q)⟩,hpq⟩ ⟨⟨j,(z,w)⟩,hzw⟩
      · change (1-u)*f (v i p-v i q)+u*g (v i p-v i q)=0
        simp only [map_sub]
        simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul] at he
        nlinarith
      · change (1-u)*f (v j z-v j w)+u*g (v j z-v j w)=0
        simp only [map_sub]
        simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul] at hezw
        nlinarith
  obtain ⟨N,hN,path,h0,h1,hmem,hedge⟩ :=
    route_of_generic_line r k v f (g-f) p0 p1 hfa hstart hfinish hties
  refine ⟨N,hN,path,h0,h1,hmem,?_⟩
  intro j hj
  obtain ⟨u,hu0,hu1,hb,hface,hadj⟩ := hedge j hj
  have hpreserve : ∀ c, (f+u • (g-f)) (comparison c)<0 := by
    intro c
    have hl : f (comparison c)<0 := hf (.inr c)
    have hr : g (comparison c)<0 := hg (.inr c)
    have hn0 := mul_neg_of_pos_of_neg (show 0<1-u by linarith) hl
    have hn1 := mul_neg_of_pos_of_neg hu0 hr
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
    nlinarith
  exact ⟨⟨f+u • (g-f),hpreserve,hb,hface⟩,hadj⟩


end HirschConstructedFibre

namespace HirschConstructedFibre
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

private lemma translated_segment (o p q : E) :
    (fun z : E => o+z) '' segment ℝ p q=segment ℝ (o+p) (o+q) := by
  apply Set.Subset.antisymm
  · rintro w ⟨z,⟨a,b,ha,hb,hab,he⟩,rfl⟩
    refine ⟨a,b,ha,hb,hab,?_⟩
    calc
      a • (o+p)+b • (o+q)=(a+b) • o+(a • p+b • q) := by module
      _=o+z := by rw [hab,one_smul,he]
  · rintro w ⟨a,b,ha,hb,hab,he⟩
    refine ⟨a • p+b • q,⟨a,b,ha,hb,hab,rfl⟩,?_⟩
    calc
      o+(a • p+b • q)=(a+b) • o+(a • p+b • q) := by rw [hab,one_smul]
      _=a • (o+p)+b • (o+q) := by module
      _=w := he

/-- A genuine fixed-core fibre route. The bound charges ONLY the added factors,
not the number of vertices in the core. Both endpoint exposures include the
same core point. All supporting segments of the FULL sum are conclusions. -/
theorem fixed_core_fibre_route
    (a r : ℕ) (core : Fin a → E) (o : Fin a) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E) (hinj : ∀ i, Function.Injective (v i))
    (p0 p1 : (i : Fin r) → Fin (k i)) (f0 g0 : E →ₗ[ℝ] ℝ)
    (hc0 : ∀ q, q≠o → f0 (core q)<f0 (core o))
    (hc1 : ∀ q, q≠o → g0 (core q)<g0 (core o))
    (hp0 : ∀ i q, q≠p0 i → f0 (v i q)<f0 (v i (p0 i)))
    (hp1 : ∀ i q, q≠p1 i → g0 (v i q)<g0 (v i (p1 i))) :
    let P := convexHull ℝ ((Finset.univ.image core : Finset E) : Set E)
    let Q := sumSet (fun i => convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E))
    let R := {z | ∃ x∈P, ∃ y∈Q, x+y=z}
    ∃ N : ℕ, N≤∑ i, (k i-1) ∧ ∃ path : ℕ → E,
      path 0=core o+∑ i, v i (p0 i) ∧ path N=core o+∑ i, v i (p1 i) ∧
      (∀ j, j≤N → path j∈R) ∧
      (∀ j, j≤N → ∃ z∈Q, path j=core o+z) ∧
      ∀ j, j<N →
        (∃ h : E →ₗ[ℝ] ℝ, (∀ z∈R, h z≤h (path j)) ∧
          supportFace R h (h (path j))=segment ℝ (path j) (path (j+1))) ∧
        Hirsch.Adj R (path j) (path (j+1)) := by
  classical
  dsimp only
  let P := convexHull ℝ ((Finset.univ.image core : Finset E) : Set E)
  let Q := sumSet (fun i => convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E))
  let R : Set E := {z | ∃ x∈P, ∃ y∈Q, x+y=z}
  let J := {q : Fin a // q≠o}
  let comp : J → E := fun q => core q.1-core o
  have hcomp0 : ∀ q, f0 (comp q)<0 := by
    intro q
    change f0 (core q.1-core o)<0
    rw [map_sub]
    exact sub_neg.mpr (hc0 q.1 q.2)
  have hcomp1 : ∀ q, g0 (comp q)<0 := by
    intro q
    change g0 (core q.1-core o)<0
    rw [map_sub]
    exact sub_neg.mpr (hc1 q.1 q.2)
  obtain ⟨N,hN,path,h0,h1,hmem,hedge⟩ :=
    finite_sum_exposed_route_preserving comp r k v hinj p0 p1 f0 g0 hp0 hp1 hcomp0 hcomp1
  have ho : core o∈P := subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨o,Finset.mem_univ _,rfl⟩)
  refine ⟨N,hN,(fun j => core o+path j),?_,?_,?_,?_,?_⟩
  · exact congrArg (fun z : E => core o+z) h0
  · exact congrArg (fun z : E => core o+z) h1
  · intro j hj
    exact ⟨core o,ho,path j,hmem j hj,rfl⟩
  · intro j hj
    exact ⟨path j,hmem j hj,rfl⟩
  · intro j hj
    obtain ⟨⟨h,hcomp,hbound,hface⟩,hadj⟩ := hedge j hj
    have hcore : ∀ x∈P, h x≤h (core o) ∧ (h x=h (core o) → x∈({core o}:Set E)) := by
      apply convexHull_support_contained _ ({core o}:Set E) h (h (core o)) (convex_singleton _)
      intro x hx
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
      by_cases he : q=o
      · subst q
        exact ⟨le_rfl,fun _ => Set.mem_singleton _⟩
      · have hv : h (core q)<h (core o) := by
          have hc := hcomp ⟨q,he⟩
          change h (core q-core o)<0 at hc
          rw [map_sub] at hc
          exact sub_neg.mp hc
        exact ⟨hv.le,fun hh => False.elim ((ne_of_lt hv) hh)⟩
    have hfull : ∀ z∈R, h z≤h (core o+path j) := by
      rintro z ⟨x,hx,y,hy,rfl⟩
      simp only [map_add]
      exact add_le_add (hcore x hx).1 (hbound y hy)
    have hslice : supportFace R h (h (core o+path j))=
        segment ℝ (core o+path j) (core o+path (j+1)) := by
      rw [← translated_segment (core o) (path j) (path (j+1))]
      apply Set.Subset.antisymm
      · rintro z ⟨⟨x,hx,y,hy,hz⟩,hs⟩
        have he : h x+h y=h (core o)+h (path j) := by
          rw [←hz,map_add,map_add] at hs
          exact hs
        have hxval : h x=h (core o) := by
          have hxle := (hcore x hx).1
          have hyle := hbound y hy
          linarith
        have hx0 : x=core o := Set.mem_singleton_iff.mp ((hcore x hx).2 hxval)
        have hyval : h y=h (path j) := by linarith
        have hymem : y∈segment ℝ (path j) (path (j+1)) := by
          rw [←hface]
          exact ⟨hy,hyval⟩
        exact ⟨y,hymem,by simpa only [hx0] using hz⟩
      · rintro z ⟨y,hy,rfl⟩
        have hy' : y∈supportFace Q h (h (path j)) := by
          rw [hface]
          exact hy
        refine ⟨⟨core o,ho,y,hy'.1,rfl⟩,?_⟩
        simp only [map_add,hy'.2]
    have hne : core o+path j≠core o+path (j+1) := by
      intro he
      exact hadj.1 (add_left_cancel he)
    exact ⟨⟨h,hfull,hslice⟩,
      adj_of_supportFace_eq_segment R h _ _ _ hne hfull hslice⟩

end HirschConstructedFibre
theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (a r : ℕ) (core : Fin a → E) (o : Fin a) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E) (hinj : ∀ i, Function.Injective (v i))
    (p0 p1 : (i : Fin r) → Fin (k i)) (f0 g0 : E →ₗ[ℝ] ℝ)
    (hc0 : ∀ q, q≠o → f0 (core q)<f0 (core o))
    (hc1 : ∀ q, q≠o → g0 (core q)<g0 (core o))
    (hp0 : ∀ i q, q≠p0 i → f0 (v i q)<f0 (v i (p0 i)))
    (hp1 : ∀ i q, q≠p1 i → g0 (v i q)<g0 (v i (p1 i))) :
    let P : Set E := convexHull ℝ ((Finset.univ.image core : Finset E) : Set E)
    let Q : Set E := {z | ∃ x : Fin r → E,
      (∀ i, x i ∈ convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E)) ∧
      (∑ i, x i)=z}
    let R : Set E := {z | ∃ x∈P, ∃ y∈Q, x+y=z}
    ∃ N : ℕ, N≤∑ i, (k i-1) ∧ ∃ path : ℕ → E,
      path 0=core o+∑ i, v i (p0 i) ∧ path N=core o+∑ i, v i (p1 i) ∧
      (∀ j, j≤N → path j∈R) ∧
      (∀ j, j≤N → ∃ z∈Q, path j=core o+z) ∧
      ∀ j, j<N →
        (∃ h : E →ₗ[ℝ] ℝ, (∀ z∈R, h z≤h (path j)) ∧
          {z | z∈R ∧ h z=h (path j)}=segment ℝ (path j) (path (j+1))) ∧
        path j≠path (j+1) ∧ IsExtreme ℝ R (segment ℝ (path j) (path (j+1))) := by
  have h := HirschConstructedFibre.fixed_core_fibre_route
    a r core o k v hinj p0 p1 f0 g0 hc0 hc1 hp0 hp1
  simpa only [HirschMinkowski.sumSet, HirschMinkowski.supportFace, Hirsch.Adj] using h

#print axioms HirschEnvelopeSequence.exists_bounded_crossing_sequence
#print axioms HirschConstructedFibre.route_of_generic_line
#print axioms HirschConstructedFibre.finite_sum_exposed_route_preserving
#print axioms HirschConstructedFibre.fixed_core_fibre_route
#print axioms solution
