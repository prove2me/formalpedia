-- Prove2me | solution 1 for Hirsch.minkowski_summand_exposed_route_contraction
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-19T01:44:08.916675+00:00
-- url     : https://prove2.me/submissions/e74048d0-521b-4ef6-ac50-048b12542d03

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Hirsch.SummandContraction

open Set

/-- The actual Minkowski sum, with no projection or decomposition oracle. -/
def sumBody {d : ℕ} (P Q : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {z | ∃ p ∈ P, ∃ q ∈ Q, p + q = z}

lemma sumBody_comm {d : ℕ} (P Q : Set (Fin d → ℝ)) :
    sumBody P Q = sumBody Q P := by
  ext z
  constructor
  · rintro ⟨p,hp,q,hq,he⟩
    exact ⟨q,hq,p,hp,(add_comm q p).trans he⟩
  · rintro ⟨q,hq,p,hp,he⟩
    exact ⟨p,hp,q,hq,(add_comm p q).trans he⟩

/-- Extremality of a sum point forces each of its components to be extreme. -/
lemma left_extreme {d : ℕ} (P Q : Set (Fin d → ℝ))
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ Q)
    (hz : p+q ∈ (sumBody P Q).extremePoints ℝ) :
    p ∈ P.extremePoints ℝ := by
  refine ⟨hp,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hs : p+q ∈ openSegment ℝ (x+q) (y+q) := by
    refine ⟨a,b,ha,hb,hab,?_⟩
    calc
      a • (x+q) + b • (y+q) = (a • x + b • y) + (a+b) • q := by module
      _ = p+q := by rw [he,hab,one_smul]
  have hh : x+q = p+q := hz.2 ⟨x,hx,q,hq,rfl⟩ ⟨y,hy,q,hq,rfl⟩ hs
  exact add_right_cancel hh

/-- Cross-sum midpoint decompositions give uniqueness, without finite lists. -/
lemma unique_split {d : ℕ} (P Q : Set (Fin d → ℝ))
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ Q)
    (hz : p+q ∈ (sumBody P Q).extremePoints ℝ)
    (x y : Fin d → ℝ) (hx : x ∈ P) (hy : y ∈ Q) (he : x+y = p+q) :
    x=p ∧ y=q := by
  have hc : (x+q)+(p+y) = (p+q)+(p+q) := by
    calc
      (x+q)+(p+y) = (x+y)+(p+q) := by module
      _ = (p+q)+(p+q) := by rw [he]
  have hmid : p+q ∈ openSegment ℝ (x+q) (p+y) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    calc
      (1/2 : ℝ) • (x+q) + (1/2 : ℝ) • (p+y) =
          (1/2 : ℝ) • ((x+q)+(p+y)) := by module
      _ = p+q := by rw [hc]; module
  have hh : x+q = p+q := hz.2 ⟨x,hx,q,hq,rfl⟩ ⟨p,hp,y,hy,rfl⟩ hmid
  have hxp : x=p := add_right_cancel hh
  refine ⟨hxp,?_⟩
  rw [hxp] at he
  exact add_left_cancel he

/-- The canonical component vertices and their uniqueness are derived. -/
theorem vertex_decomposition {d : ℕ} (P Q : Set (Fin d → ℝ))
    (z : Fin d → ℝ) (hz : z ∈ (sumBody P Q).extremePoints ℝ) :
    ∃ p q : Fin d → ℝ, p ∈ P.extremePoints ℝ ∧ q ∈ Q.extremePoints ℝ ∧
      p+q=z ∧ ∀ x ∈ P, ∀ y ∈ Q, x+y=z → x=p ∧ y=q := by
  obtain ⟨p,hp,q,hq,he⟩ := hz.1
  have hz' : p+q ∈ (sumBody P Q).extremePoints ℝ := he.symm ▸ hz
  have hqp : q+p ∈ (sumBody Q P).extremePoints ℝ := by
    rw [sumBody_comm Q P,add_comm q p]
    exact hz'
  refine ⟨p,q,left_extreme P Q p q hp hq hz',
    left_extreme Q P q p hq hp hqp,he,?_⟩
  intro x hx y hy hxy
  exact unique_split P Q p q hp hq hz' x y hx hy (hxy.trans he.symm)

private lemma segment_parameter {d : ℕ} (u v z : Fin d → ℝ)
    (hz : z ∈ segment ℝ u v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = u + t • (v-u) := by
  obtain ⟨s,t,hs,ht,hst,he⟩ := hz
  refine ⟨t,ht,by linarith,?_⟩
  have hs' : s = 1-t := by linarith
  rw [← he,hs']
  module

private lemma line_injective {d : ℕ} (D : Fin d → ℝ) (hD : D ≠ 0) :
    Function.Injective (fun t : ℝ => t • D) := by
  have hex : ∃ i, D i ≠ 0 := by
    by_contra hn
    apply hD
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  intro s t he
  have hh := congrFun he i
  change s * D i = t * D i at hh
  exact mul_right_cancel₀ hi hh

/-- A whole exposed sum segment forces its component support face to be a
whole segment, including the collapsed singleton case. No face/rank oracle. -/
theorem left_face_of_sum_edge {d : ℕ} (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (p₀ p₁ q₀ q₁ : Fin d → ℝ)
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q)
    (hne : p₀+q₀ ≠ p₁+q₁)
    (hex : IsExposed ℝ (sumBody P Q) (segment ℝ (p₀+q₀) (p₁+q₁))) :
    IsExposed ℝ P (segment ℝ p₀ p₁) ∧
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        p₁-p₀ = α • ((p₁+q₁)-(p₀+q₀)) ∧
        q₁-q₀ = (1-α) • ((p₁+q₁)-(p₀+q₀)) := by
  obtain ⟨f,hface⟩ := hex ⟨p₀+q₀,left_mem_segment ℝ _ _⟩
  have hleft : p₀+q₀ ∈ sumBody P Q ∧
      ∀ z ∈ sumBody P Q, f z ≤ f (p₀+q₀) := by
    change p₀+q₀ ∈ {x ∈ sumBody P Q | ∀ y ∈ sumBody P Q, f y ≤ f x}
    rw [← hface]
    exact left_mem_segment ℝ _ _
  have hright : p₁+q₁ ∈ sumBody P Q ∧
      ∀ z ∈ sumBody P Q, f z ≤ f (p₁+q₁) := by
    change p₁+q₁ ∈ {x ∈ sumBody P Q | ∀ y ∈ sumBody P Q, f y ≤ f x}
    rw [← hface]
    exact right_mem_segment ℝ _ _
  have htotal : f (p₀+q₀) = f (p₁+q₁) :=
    le_antisymm (hright.2 _ hleft.1) (hleft.2 _ hright.1)
  have hpmax : ∀ x ∈ P, f x ≤ f p₀ := by
    intro x hx
    have h := hleft.2 (x+q₀) ⟨x,hx,q₀,hq₀,rfl⟩
    simp only [map_add] at h
    linarith
  have hqmax : ∀ y ∈ Q, f y ≤ f q₀ := by
    intro y hy
    have h := hleft.2 (p₀+y) ⟨p₀,hp₀,y,hy,rfl⟩
    simp only [map_add] at h
    linarith
  have hpval : f p₁ = f p₀ := by
    have h1 := hpmax p₁ hp₁
    have h2 := hqmax q₁ hq₁
    simp only [map_add] at htotal
    linarith
  have hqval : f q₁ = f q₀ := by
    simp only [map_add] at htotal
    linarith
  have hsumseg : ∀ x ∈ P, f x = f p₀ → ∀ y ∈ Q, f y = f q₀ →
      x+y ∈ segment ℝ (p₀+q₀) (p₁+q₁) := by
    intro x hx hfx y hy hfy
    rw [hface]
    refine ⟨⟨x,hx,y,hy,rfl⟩,?_⟩
    intro z hz
    have h := hleft.2 z hz
    simpa only [map_add,hfx,hfy] using h
  let D := (p₁+q₁)-(p₀+q₀)
  have hD : D ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp hz).symm
  obtain ⟨α,ha0,ha1,hcross⟩ := segment_parameter _ _ _
    (hsumseg p₁ hp₁ hpval q₀ hq₀ rfl)
  have hpdisp : p₁-p₀ = α • D := by
    calc
      p₁-p₀ = (p₁+q₀)-(p₀+q₀) := by module
      _ = α • D := by rw [hcross]; module
  have hqdisp : q₁-q₀ = (1-α) • D := by
    calc
      q₁-q₀ = D-(p₁-p₀) := by dsimp only [D]; module
      _ = (1-α) • D := by rw [hpdisp]; module
  have hfaceP : segment ℝ p₀ p₁ = {x ∈ P | ∀ y ∈ P, f y ≤ f x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨s,t,hs,ht,hst,he⟩ := hx
      have hxP : x ∈ P := he ▸ hP hp₀ hp₁ hs ht hst
      have hfx : f x = f p₀ := by
        rw [← he]
        simp only [map_add,map_smul,smul_eq_mul,hpval]
        rw [← add_mul,hst,one_mul]
      exact ⟨hxP,fun y hy => (hpmax y hy).trans_eq hfx.symm⟩
    · rintro ⟨hxP,hmax⟩
      have hfx : f x = f p₀ := le_antisymm (hpmax x hxP) (hmax p₀ hp₀)
      obtain ⟨s,hs0,hs1,hs⟩ := segment_parameter _ _ _
        (hsumseg x hxP hfx q₀ hq₀ rfl)
      obtain ⟨t,ht0,ht1,ht⟩ := segment_parameter _ _ _
        (hsumseg x hxP hfx q₁ hq₁ hqval)
      have hxdisp : x-p₀ = s • D := by
        calc
          x-p₀ = (x+q₀)-(p₀+q₀) := by module
          _ = s • D := by rw [hs]; module
      have htcoef : t = s + (1-α) := by
        apply line_injective D hD
        calc
          t • D = (x+q₁)-(p₀+q₀) := by rw [ht]; module
          _ = ((x+q₀)-(p₀+q₀))+(q₁-q₀) := by module
          _ = s • D+(1-α) • D := by rw [hs,hqdisp]; module
          _ = (s+(1-α)) • D := by module
      have hsa : s ≤ α := by linarith
      by_cases ha : α = 0
      · have hs0' : s = 0 := by linarith
        rw [hs0',zero_smul] at hxdisp
        rw [sub_eq_zero.mp hxdisp]
        exact left_mem_segment ℝ _ _
      · have hap : 0 < α := lt_of_le_of_ne ha0 (Ne.symm ha)
        have hr0 : 0 ≤ s/α := div_nonneg hs0 ha0
        have hr1 : s/α ≤ 1 := (div_le_one hap).mpr hsa
        have hmul : (s/α)*α = s := div_mul_cancel₀ s ha
        have hp₁eq : p₁ = p₀+α • D := by rw [← hpdisp]; module
        have hxeq : x = p₀+s • D := by rw [← hxdisp]; module
        refine ⟨1-s/α,s/α,by linarith,hr0,by ring,?_⟩
        rw [hp₁eq,hxeq]
        simp only [smul_add,smul_smul,hmul]
        module
  exact ⟨fun _ => ⟨f,hfaceP⟩,α,ha0,ha1,hpdisp,hqdisp⟩

/-- Both component segments inherit actual exposedness; their displacements
are cooriented nonnegative fractions of the original sum-edge displacement. -/
theorem split_exposed_edge {d : ℕ} (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (p₀ p₁ q₀ q₁ : Fin d → ℝ)
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q)
    (hne : p₀+q₀ ≠ p₁+q₁)
    (hex : IsExposed ℝ (sumBody P Q) (segment ℝ (p₀+q₀) (p₁+q₁))) :
    IsExposed ℝ P (segment ℝ p₀ p₁) ∧ IsExposed ℝ Q (segment ℝ q₀ q₁) ∧
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        p₁-p₀ = α • ((p₁+q₁)-(p₀+q₀)) ∧
        q₁-q₀ = (1-α) • ((p₁+q₁)-(p₀+q₀)) := by
  have hleft := left_face_of_sum_edge P Q hP p₀ p₁ q₀ q₁ hp₀ hp₁ hq₀ hq₁ hne hex
  have hn : q₀+p₀ ≠ q₁+p₁ := by simpa only [add_comm] using hne
  have he : IsExposed ℝ (sumBody Q P) (segment ℝ (q₀+p₀) (q₁+p₁)) := by
    rw [sumBody_comm Q P,add_comm q₀ p₀,add_comm q₁ p₁]
    exact hex
  have hright := left_face_of_sum_edge Q P hQ q₀ q₁ p₀ p₁ hq₀ hq₁ hp₀ hp₁ hn he
  exact ⟨hleft.1,hright.1,hleft.2⟩

-- Reused verbatim from ACCEPTED #306; only the containing namespace differs.
/-- Delete stationary transitions from an explicitly supplied finite schedule.
This helper proves compression; the schedule itself is constructed below. -/
private lemma compress_schedule {E : Type*} (valid : E → Prop) (edge : E → E → Prop)
    (N : ℕ) (a : ℕ → E)
    (hv : ∀ i, i ≤ N → valid (a i))
    (he : ∀ i, i < N → a i = a (i+1) ∨ edge (a i) (a (i+1))) :
    ∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → E,
      p 0 = a 0 ∧ p L = a N ∧ (∀ i, i ≤ L → valid (p i)) ∧
      ∀ i, i < L → edge (p i) (p (i+1)) := by
  induction N generalizing a with
  | zero =>
    refine ⟨0, le_rfl, a, rfl, rfl, hv, ?_⟩
    intro i hi
    omega
  | succ N ih =>
    obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ := ih (fun i => a (i+1))
      (fun i hi => hv (i+1) (by omega)) (fun i hi => he (i+1) (by omega))
    rcases he 0 (by omega) with h | h
    · refine ⟨L, by omega, p, hp0.trans h.symm, hpL, hpv, hpe⟩
    · let q : ℕ → E := fun i => match i with
        | 0 => a 0
        | j+1 => p j
      refine ⟨L+1, by omega, q, rfl, hpL, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hv 0 (by omega)
        | succ i => exact hpv i (by omega)
      · intro i hi
        cases i with
        | zero => simpa only [q, hp0] using h
        | succ i => exact hpe i (by omega)

/-- Canonical decomposition contracts an actual sum walk into two actual
summand walks. Stationary component steps are deleted, never called edges. -/
theorem contract_route (d N : ℕ) (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (z : ℕ → (Fin d → ℝ))
    (hz : ∀ i, i ≤ N → z i ∈ (sumBody P Q).extremePoints ℝ)
    (he : ∀ i, i < N → z i ≠ z (i+1) ∧
      IsExposed ℝ (sumBody P Q) (segment ℝ (z i) (z (i+1)))) :
    ∃ a b : ℕ → (Fin d → ℝ),
      (∀ i, i ≤ N → a i ∈ P.extremePoints ℝ ∧ b i ∈ Q.extremePoints ℝ ∧
        a i+b i=z i ∧ ∀ x ∈ P, ∀ y ∈ Q, x+y=z i → x=a i ∧ y=b i) ∧
      (∀ i, i < N →
        IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
        IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
        ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
          a (i+1)-a i = α • (z (i+1)-z i) ∧
          b (i+1)-b i = (1-α) • (z (i+1)-z i)) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=a 0 ∧ p L=a N ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=b 0 ∧ p L=b N ∧ (∀ i, i ≤ L → p i ∈ Q.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ Q (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ Q (segment ℝ (p i) (p (i+1)))) := by
  classical
  have hchoose : ∀ i : ℕ, ∃ p q : Fin d → ℝ, i ≤ N →
      p ∈ P.extremePoints ℝ ∧ q ∈ Q.extremePoints ℝ ∧ p+q=z i ∧
        ∀ x ∈ P, ∀ y ∈ Q, x+y=z i → x=p ∧ y=q := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨p,q,hp,hq,hs,hu⟩ := vertex_decomposition P Q (z i) (hz i hi)
      exact ⟨p,q,fun _ => ⟨hp,hq,hs,hu⟩⟩
    · exact ⟨0,0,fun hh => False.elim (hi hh)⟩
  choose a b hab using hchoose
  have hsplit : ∀ i, i < N →
      IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
      IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        a (i+1)-a i = α • (z (i+1)-z i) ∧
        b (i+1)-b i = (1-α) • (z (i+1)-z i) := by
    intro i hi
    have h0 := hab i (show i ≤ N by omega)
    have h1 := hab (i+1) (show i+1 ≤ N by omega)
    have hne : a i+b i ≠ a (i+1)+b (i+1) := by
      rw [h0.2.2.1,h1.2.2.1]
      exact (he i hi).1
    have hex : IsExposed ℝ (sumBody P Q)
        (segment ℝ (a i+b i) (a (i+1)+b (i+1))) := by
      rw [h0.2.2.1,h1.2.2.1]
      exact (he i hi).2
    have hs := split_exposed_edge P Q hP hQ (a i) (a (i+1)) (b i) (b (i+1))
      h0.1.1 h1.1.1 h0.2.1.1 h1.2.1.1 hne hex
    simpa only [h0.2.2.1,h1.2.2.1] using hs
  have hA : ∀ i, i < N → a i=a (i+1) ∨
      (a i ≠ a (i+1) ∧ IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
        IsExtreme ℝ P (segment ℝ (a i) (a (i+1)))) := by
    intro i hi
    by_cases h : a i=a (i+1)
    · exact Or.inl h
    · exact Or.inr ⟨h,(hsplit i hi).1,(hsplit i hi).1.isExtreme⟩
  have hB : ∀ i, i < N → b i=b (i+1) ∨
      (b i ≠ b (i+1) ∧ IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
        IsExtreme ℝ Q (segment ℝ (b i) (b (i+1)))) := by
    intro i hi
    by_cases h : b i=b (i+1)
    · exact Or.inl h
    · exact Or.inr ⟨h,(hsplit i hi).2.1,(hsplit i hi).2.1.isExtreme⟩
  obtain ⟨LA,hLA,pA,hA0,hAN,hAv,hAe⟩ := compress_schedule
    (fun x => x ∈ P.extremePoints ℝ)
    (fun x y => x ≠ y ∧ IsExposed ℝ P (segment ℝ x y) ∧ IsExtreme ℝ P (segment ℝ x y))
    N a (fun i hi => (hab i hi).1) hA
  obtain ⟨LB,hLB,pB,hB0,hBN,hBv,hBe⟩ := compress_schedule
    (fun x => x ∈ Q.extremePoints ℝ)
    (fun x y => x ≠ y ∧ IsExposed ℝ Q (segment ℝ x y) ∧ IsExtreme ℝ Q (segment ℝ x y))
    N b (fun i hi => (hab i hi).2.1) hB
  exact ⟨a,b,hab,hsplit,⟨LA,hLA,pA,hA0,hAN,hAv,hAe⟩,
    ⟨LB,hLB,pB,hB0,hBN,hBv,hBe⟩⟩

end Hirsch.SummandContraction

/-- Actual Minkowski decomposition, unlike arbitrary linear projection,
contracts exposed-edge vertex walks without increasing either route length. -/
theorem solution (d N : ℕ) (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (z : ℕ → (Fin d → ℝ))
    (hz : ∀ i, i ≤ N → z i ∈
      ({w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w}).extremePoints ℝ)
    (he : ∀ i, i < N → z i ≠ z (i+1) ∧
      IsExposed ℝ {w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w} (segment ℝ (z i) (z (i+1)))) :
    ∃ a b : ℕ → (Fin d → ℝ),
      (∀ i, i ≤ N → a i ∈ P.extremePoints ℝ ∧ b i ∈ Q.extremePoints ℝ ∧
        a i+b i=z i ∧ ∀ x ∈ P, ∀ y ∈ Q, x+y=z i → x=a i ∧ y=b i) ∧
      (∀ i, i < N →
        IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
        IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
        ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
          a (i+1)-a i = α • (z (i+1)-z i) ∧
          b (i+1)-b i = (1-α) • (z (i+1)-z i)) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=a 0 ∧ p L=a N ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=b 0 ∧ p L=b N ∧ (∀ i, i ≤ L → p i ∈ Q.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ Q (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ Q (segment ℝ (p i) (p (i+1)))) := by
  exact Hirsch.SummandContraction.contract_route d N P Q hP hQ z hz he

#print axioms Hirsch.SummandContraction.vertex_decomposition
#print axioms Hirsch.SummandContraction.left_face_of_sum_edge
#print axioms Hirsch.SummandContraction.split_exposed_edge
#print axioms Hirsch.SummandContraction.contract_route
#print axioms solution
