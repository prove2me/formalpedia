-- Prove2me | solution 1 for Hirsch.finite_hull_pair_segment_completion
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-19T05:03:17.59898+00:00
-- url     : https://prove2.me/submissions/0307a57f-c4be-4cf2-ac81-80e04b743201

import Mathlib

open scoped BigOperators Pointwise
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Hirsch.PairSegmentCompletion

open Set

abbrev Pair (n : ℕ) := Fin n × Fin n

def box (n : ℕ) : Set (Pair n → ℝ) := Icc 0 1

def point {d n : ℕ} (v : Fin n → (Fin d → ℝ)) (t : Pair n → ℝ) : Fin d → ℝ :=
  ∑ e : Pair n, ((t e) • v e.1 + (1-t e) • v e.2)

def zonotope {d n : ℕ} (v : Fin n → (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  point v '' box n

def erosion {d n : ℕ} (v : Fin n → (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {q | ∀ i, q + v i ∈ zonotope v}

lemma mem_box {n : ℕ} (t : Pair n → ℝ) :
    t ∈ box n ↔ ∀ e, 0 ≤ t e ∧ t e ≤ 1 := by
  constructor
  · intro ht e
    exact ⟨ht.1 e,ht.2 e⟩
  · intro ht
    exact ⟨fun e => (ht e).1,fun e => (ht e).2⟩

/-- The construction is an actual sum of represented closed segments. -/
lemma compact_zonotope {d n : ℕ} (v : Fin n → (Fin d → ℝ)) :
    IsCompact (zonotope v) := by
  have hc : IsCompact (box n) := isCompact_Icc
  apply hc.image
  unfold point
  fun_prop

lemma point_combo {d n : ℕ} (v : Fin n → (Fin d → ℝ))
    (s t : Pair n → ℝ) (a b : ℝ) (hab : a+b=1) :
    point v (a • s+b • t) = a • point v s+b • point v t := by
  have ha : a=1-b := by linarith
  calc
    point v (a • s+b • t) =
        ∑ e : Pair n, (a • (s e • v e.1+(1-s e) • v e.2) +
          b • (t e • v e.1+(1-t e) • v e.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      change (a*s e+b*t e) • v e.1+(1-(a*s e+b*t e)) • v e.2 = _
      rw [ha]
      module
    _ = a • point v s+b • point v t := by
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (fun x y : Fin d → ℝ => x+y)
        (Finset.smul_sum (r:=a) (s:=Finset.univ)
          (f:=fun e : Pair n => s e • v e.1+(1-s e) • v e.2)).symm
        (Finset.smul_sum (r:=b) (s:=Finset.univ)
          (f:=fun e : Pair n => t e • v e.1+(1-t e) • v e.2)).symm

lemma convex_zonotope {d n : ℕ} (v : Fin n → (Fin d → ℝ)) :
    Convex ℝ (zonotope v) := by
  rintro x ⟨s,hs,rfl⟩ y ⟨t,ht,rfl⟩ a b ha hb hab
  refine ⟨a • s+b • t,?_,point_combo v s t a b hab⟩
  apply (mem_box _).mpr
  intro e
  have hs' := (mem_box s).mp hs e
  have ht' := (mem_box t).mp ht e
  change 0 ≤ a*s e+b*t e ∧ a*s e+b*t e ≤ 1
  constructor
  · exact add_nonneg (mul_nonneg ha hs'.1) (mul_nonneg hb ht'.1)
  · calc
      a*s e+b*t e ≤ a*1+b*1 := add_le_add
        (mul_le_mul_of_nonneg_left hs'.2 ha) (mul_le_mul_of_nonneg_left ht'.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

lemma shift_combo {d : ℕ} (x y p : Fin d → ℝ) (a b : ℝ) (hab : a+b=1) :
    a • (x+p)+b • (y+p) = (a • x+b • y)+p := by
  calc
    a • (x+p)+b • (y+p) = (a • x+b • y)+(a+b) • p := by module
    _ = (a • x+b • y)+p := by rw [hab,one_smul]

lemma convex_erosion {d n : ℕ} (v : Fin n → (Fin d → ℝ)) :
    Convex ℝ (erosion v) := by
  intro x hx y hy a b ha hb hab i
  rw [← shift_combo x y (v i) a b hab]
  exact convex_zonotope v (hx i) (hy i) ha hb hab

lemma closed_erosion {d n : ℕ} (v : Fin n → (Fin d → ℝ)) :
    IsClosed (erosion v) := by
  have he : erosion v = ⋂ i : Fin n, (fun q => q+v i) ⁻¹' zonotope v := by
    ext q
    simp only [erosion,mem_setOf_eq,mem_iInter,mem_preimage]
  rw [he]
  exact isClosed_iInter (fun i => (compact_zonotope v).isClosed.preimage (by fun_prop))

lemma compact_erosion {d n : ℕ} (hn : 0 < n) (v : Fin n → (Fin d → ℝ)) :
    IsCompact (erosion v) := by
  let i₀ : Fin n := ⟨0,hn⟩
  have hK : IsCompact ((fun z : Fin d → ℝ => z-v i₀) '' zonotope v) :=
    (compact_zonotope v).image (by fun_prop)
  apply hK.of_isClosed_subset (closed_erosion v)
  intro q hq
  exact ⟨q+v i₀,hq i₀,by simp⟩

/-- Testing the generators gives translation of the WHOLE convex hull. -/
lemma translate_hull {d n : ℕ} (v : Fin n → (Fin d → ℝ))
    (q : Fin d → ℝ) (hq : q ∈ erosion v) :
    ∀ p ∈ convexHull ℝ (range v), p+q ∈ zonotope v := by
  have hc : Convex ℝ {p : Fin d → ℝ | p+q ∈ zonotope v} := by
    intro x hx y hy a b ha hb hab
    change (a • x+b • y)+q ∈ zonotope v
    rw [← shift_combo x y q a b hab]
    exact convex_zonotope v hx hy ha hb hab
  apply convexHull_min _ hc
  rintro p ⟨i,rfl⟩
  simpa only [add_comm] using hq i

/-- Replacing one segment endpoint gives an exact translate, not a projection. -/
lemma replace_endpoint {d n : ℕ} (v : Fin n → (Fin d → ℝ))
    (t : Pair n → ℝ) (k i : Fin n) (ht : t (k,i)=1) :
    point v (Function.update t (k,i) 0) = point v t-v k+v i := by
  classical
  have he : ∀ e : Pair n,
      (Function.update t (k,i) 0 e) • v e.1 +
        (1-Function.update t (k,i) 0 e) • v e.2 =
      (t e • v e.1+(1-t e) • v e.2) +
        if e=(k,i) then v i-v k else 0 := by
    intro e
    by_cases h : e=(k,i)
    · subst e
      change (Function.update t (k,i) 0 (k,i)) • v k +
        (1-Function.update t (k,i) 0 (k,i)) • v i =
        (t (k,i) • v k+(1-t (k,i)) • v i) +
        (if (k,i)=(k,i) then v i-v k else 0)
      rw [Function.update_self,ht,if_pos rfl]
      simp only [zero_smul,sub_zero,one_smul,sub_self,add_zero,zero_add]
      abel
    · simp only [Function.update_of_ne h,if_neg h,add_zero]
  calc
    point v (Function.update t (k,i) 0) =
        ∑ e : Pair n, ((t e • v e.1+(1-t e) • v e.2) +
          if e=(k,i) then v i-v k else 0) := Finset.sum_congr rfl (fun e _ => he e)
    _ = point v t+(v i-v k) := by
      rw [Finset.sum_add_distrib]
      simp [point]
    _ = point v t-v k+v i := by module

/-- Every objective gets a maximizing sum point whose translate contains
ALL generators. This proves a genuine support-attaining erosion witness. -/
theorem support_witness {d n : ℕ} (hn : 0 < n) (v : Fin n → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    ∃ k : Fin n, ∃ q ∈ erosion v,
      v k+q ∈ zonotope v ∧ ∀ z ∈ zonotope v, f z ≤ f (v k+q) := by
  classical
  obtain ⟨k,_,hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => f (v i)) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hk' : ∀ i, f (v i) ≤ f (v k) := fun i => hk i (Finset.mem_univ i)
  let t : Pair n → ℝ := fun e =>
    if e.1=k then 1 else if f (v e.1) < f (v e.2) then 0 else 1
  have htb : t ∈ box n := by
    apply (mem_box t).mpr
    intro e
    dsimp only [t]
    split_ifs <;> norm_num
  have hsel : ∀ e : Pair n,
      f (v e.1) ≤ f (t e • v e.1+(1-t e) • v e.2) ∧
      f (v e.2) ≤ f (t e • v e.1+(1-t e) • v e.2) := by
    intro e
    by_cases h : e.1=k
    · have ht : t e=1 := by simp only [t,if_pos h]
      simp only [ht,one_smul,sub_self,zero_smul,add_zero]
      exact ⟨le_rfl,by simpa only [h] using hk' e.2⟩
    · by_cases hlt : f (v e.1) < f (v e.2)
      · have ht : t e=0 := by simp only [t,if_neg h,if_pos hlt]
        simp only [ht,zero_smul,sub_zero,one_smul,zero_add]
        exact ⟨hlt.le,le_rfl⟩
      · have ht : t e=1 := by simp only [t,if_neg h,if_neg hlt]
        simp only [ht,one_smul,sub_self,zero_smul,add_zero]
        exact ⟨le_rfl,le_of_not_gt hlt⟩
  have hmax : ∀ z ∈ zonotope v, f z ≤ f (point v t) := by
    rintro z ⟨s,hs,rfl⟩
    simp only [point,map_sum]
    apply Finset.sum_le_sum
    intro e _
    have hs' := (mem_box s).mp hs e
    have he := hsel e
    rw [map_add,map_smul,map_smul]
    change s e*f (v e.1)+(1-s e)*f (v e.2) ≤ _
    calc
      s e*f (v e.1)+(1-s e)*f (v e.2) ≤
          s e*f (t e • v e.1+(1-t e) • v e.2)+
          (1-s e)*f (t e • v e.1+(1-t e) • v e.2) :=
        add_le_add (mul_le_mul_of_nonneg_left he.1 hs'.1)
          (mul_le_mul_of_nonneg_left he.2 (sub_nonneg.mpr hs'.2))
      _ = f (t e • v e.1+(1-t e) • v e.2) := by ring
  let q := point v t-v k
  have hq : q ∈ erosion v := by
    intro i
    have htki : t (k,i)=1 := by simp [t]
    have hnew : Function.update t (k,i) 0 ∈ box n := by
      apply (mem_box _).mpr
      intro e
      by_cases he : e=(k,i)
      · subst e
        simp only [Function.update_self]
        norm_num
      · simpa only [Function.update_of_ne he] using (mem_box t).mp htb e
    refine ⟨Function.update t (k,i) 0,hnew,?_⟩
    exact replace_endpoint v t k i htki
  have heq : v k+q=point v t := by dsimp only [q]; module
  refine ⟨k,q,hq,?_,?_⟩
  · rw [heq]
    exact ⟨t,htb,rfl⟩
  · intro z hz
    rw [heq]
    exact hmax z hz

/-- The explicit erosion is a nonempty compact convex summand; equality is
proved by strict separation after constructing every support witness. -/
theorem completion {d n : ℕ} (hn : 0 < n) (v : Fin n → (Fin d → ℝ)) :
    IsCompact (zonotope v) ∧ Convex ℝ (zonotope v) ∧
    IsCompact (erosion v) ∧ Convex ℝ (erosion v) ∧ (erosion v).Nonempty ∧
    zonotope v = convexHull ℝ (range v)+erosion v := by
  have hZc := compact_zonotope v
  have hZv := convex_zonotope v
  have hQc := compact_erosion hn v
  have hQv := convex_erosion v
  obtain ⟨k,q,hq,_,_⟩ := support_witness hn v (0 : (Fin d → ℝ) →ₗ[ℝ] ℝ)
  refine ⟨hZc,hZv,hQc,hQv,⟨q,hq⟩,?_⟩
  have hPc : IsCompact (convexHull ℝ (range v)) := (finite_range v).isCompact_convexHull ℝ
  have hPv : Convex ℝ (convexHull ℝ (range v)) := convex_convexHull ℝ _
  apply Subset.antisymm
  · intro z hz
    by_contra hnz
    obtain ⟨f,c,hf,hfz⟩ := geometric_hahn_banach_closed_point
      (hPv.add hQv) (hPc.add hQc).isClosed hnz
    obtain ⟨j,r,hr,_,hmax⟩ := support_witness hn v f.toLinearMap
    have hmem : v j+r ∈ convexHull ℝ (range v)+erosion v :=
      ⟨v j,subset_convexHull ℝ (range v) ⟨j,rfl⟩,r,hr,rfl⟩
    have hlt := hf (v j+r) hmem
    have hle := hmax z hz
    change f z ≤ f (v j+r) at hle
    linarith
  · rintro z ⟨p,hp,r,hr,rfl⟩
    exact translate_hull v r hr p hp

end Hirsch.PairSegmentCompletion

/-- Every nonempty finite convex hull has the displayed actual segment-sum
completion, with a proved nonempty compact convex erosion, not a supplied one. -/
theorem solution (d n : ℕ) (hn : 0 < n) (v : Fin n → (Fin d → ℝ)) :
    let Z : Set (Fin d → ℝ) :=
      {z | ∃ t : (Fin n × Fin n) → ℝ,
        (∀ e, 0 ≤ t e ∧ t e ≤ 1) ∧
        (∑ e : Fin n × Fin n, (t e • v e.1+(1-t e) • v e.2))=z}
    let Q : Set (Fin d → ℝ) := {q | ∀ i, q+v i ∈ Z}
    IsCompact Z ∧ Convex ℝ Z ∧ IsCompact Q ∧ Convex ℝ Q ∧ Q.Nonempty ∧
      Z = {z | ∃ p ∈ convexHull ℝ (Set.range v), ∃ q ∈ Q, p+q=z} ∧
      Fintype.card (Fin n × Fin n) = n^2 := by
  classical
  let Z : Set (Fin d → ℝ) := {z | ∃ t : (Fin n × Fin n) → ℝ,
    (∀ e, 0 ≤ t e ∧ t e ≤ 1) ∧
    (∑ e : Fin n × Fin n, (t e • v e.1+(1-t e) • v e.2))=z}
  have hZ : Hirsch.PairSegmentCompletion.zonotope v = Z := by
    ext z
    simp only [Z,Hirsch.PairSegmentCompletion.zonotope,Set.mem_image,
      Hirsch.PairSegmentCompletion.mem_box,Hirsch.PairSegmentCompletion.point,Set.mem_setOf_eq]
  have hQ : Hirsch.PairSegmentCompletion.erosion v = {q | ∀ i, q+v i ∈ Z} := by
    unfold Hirsch.PairSegmentCompletion.erosion
    rw [hZ]
  have h := Hirsch.PairSegmentCompletion.completion hn v
  rw [hZ,hQ] at h
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · exact h.2.2.2.2.2
  · simp [pow_two]

#print axioms Hirsch.PairSegmentCompletion.compact_zonotope
#print axioms Hirsch.PairSegmentCompletion.translate_hull
#print axioms Hirsch.PairSegmentCompletion.support_witness
#print axioms Hirsch.PairSegmentCompletion.completion
#print axioms solution
