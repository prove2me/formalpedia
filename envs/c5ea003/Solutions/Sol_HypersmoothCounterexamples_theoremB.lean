-- Prove2me | solution 1 for HypersmoothCounterexamples.theoremB
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-26T02:12:26.176796+00:00
-- url     : https://prove2.me/submissions/16493c6c-8809-4ee0-a8ef-eb49be793d2c

import Definitions.Def_Hypersmooth20261125
import Definitions.Def_QuadrantShifts20261125
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Order.Compact

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarGeometry
section
                                             

set_option autoImplicit false

namespace HypersmoothCounterexamples

theorem diagonalStart_ge (n : ℕ) : n ≤ diagonalStart n := by
  induction n with
  | zero => omega
  | succ n ih => rw [diagonalStart_succ]; omega

theorem increasing_equal_translation_of_tail {s t : Increasing} {n : ℕ}
    (h : ∀ k, n ≤ k → s.val k = t.val k) :
    ∀ v, planarLabel s (v + (n, 0)) = planarLabel t (v + (n, 0)) := by
  intro v
  apply h
  change n ≤ diagonalStart (v.1 + n + (v.2 + 0)) + (v.2 + 0)
  have h' := diagonalStart_ge (v.1 + n + (v.2 + 0))
  omega

theorem increasing_overlap_translation {s t : Increasing}
    (h : ∀ n j : ℕ, j < n →
      s.val (diagonalStart n + j + 1) = t.val (diagonalStart n + j)) :
    ∀ v, planarLabel s (v + (0, 1)) = planarLabel t (v + (1, 0)) := by
  intro v
  change s.val (diagonalStart ((v.1+0)+(v.2+1))+(v.2+1)) =
    t.val (diagonalStart ((v.1+1)+(v.2+0))+(v.2+0))
  rw [show (v.1+0)+(v.2+1) = v.1+v.2+1 by omega,
    show (v.1+1)+(v.2+0) = v.1+v.2+1 by omega, Nat.add_zero, ← Nat.add_assoc]
  exact h (v.1+v.2+1) v.2 (by omega)

def planarPoint (s : Increasing) : PlanarArrays := ⟨planarLabel s, ⟨s, rfl⟩⟩

@[simp] theorem planarPoint_val (s : Increasing) : (planarPoint s).val = planarLabel s := rfl

theorem continuous_planarLabel : Continuous planarLabel := by
  apply continuous_pi
  intro v
  exact (continuous_apply (siteIndex v)).comp continuous_subtype_val

theorem continuous_planarPoint : Continuous planarPoint :=
  continuous_planarLabel.subtype_mk _

noncomputable def planarRead (x : PlanarArrays) : Increasing :=
  ⟨fun n => x.val (siteEquiv.symm n), by
    obtain ⟨s, hs⟩ := x.property
    have heq : (fun n => x.val (siteEquiv.symm n)) = s.val := by
      rw [← hs]
      funext n
      change s.val (siteEquiv (siteEquiv.symm n)) = s.val n
      rw [Equiv.apply_symm_apply]
    rw [heq]
    exact s.property⟩

theorem continuous_planarRead : Continuous planarRead := by
  apply Continuous.subtype_mk
  exact continuous_pi fun n => (continuous_apply (siteEquiv.symm n)).comp continuous_subtype_val

@[simp] theorem planarRead_planarPoint (s : Increasing) : planarRead (planarPoint s) = s := by
  apply Subtype.ext
  funext n
  change s.val (siteEquiv (siteEquiv.symm n)) = s.val n
  rw [Equiv.apply_symm_apply]

@[simp] theorem planarPoint_planarRead (x : PlanarArrays) : planarPoint (planarRead x) = x := by
  apply Subtype.ext
  funext v
  change x.val (siteEquiv.symm (siteEquiv v)) = x.val v
  rw [Equiv.symm_apply_apply]

noncomputable def planarHomeomorph : Increasing ≃ₜ PlanarArrays where
  toEquiv := ⟨planarPoint, planarRead, planarRead_planarPoint, planarPoint_planarRead⟩
  continuous_toFun := continuous_planarPoint
  continuous_invFun := continuous_planarRead

theorem increasingRelation_iff_planarRelation (s t : Increasing) :
    IncreasingRelation s t ↔ PlanarRelation (planarPoint s) (planarPoint t) := by
  constructor
  · rintro ⟨a,b,h⟩
    exact ⟨a,b,funext h⟩
  · rintro ⟨a,b,h⟩
    exact ⟨a,b,congrFun h⟩

theorem planarLabel_free (s : Increasing) : HasFreeTranslates (planarLabel s) := by
  intro a b hab
  apply siteIndex_injective
  apply s.property.injective
  simpa [planarLabel, forward] using congrFun hab (0 : ℕ × ℕ)

theorem continuous_planarShift (a : ℕ × ℕ) : Continuous (planarShift a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun v => (continuous_apply (v+a)).comp continuous_subtype_val

theorem planarShift_commute (a b : ℕ × ℕ) : Function.Commute (planarShift a) (planarShift b) := by
  intro x
  apply Subtype.ext
  funext v
  change x.val ((v+a)+b) = x.val ((v+b)+a)
  rw [add_right_comm]

theorem commonFuture_equivalence {I A : Type*} [AddCommMonoid I] :
    Equivalence (CommonFuture : (I → A) → (I → A) → Prop) := by
  refine ⟨fun x => ⟨0,0,rfl⟩, ?_, ?_⟩
  · rintro x y ⟨a,b,h⟩
    exact ⟨b,a,h.symm⟩
  · rintro x y z ⟨a,b,hab⟩ ⟨c,d,hcd⟩
    refine ⟨c+a,b+d,funext fun v => ?_⟩
    have h₁ := congrFun hab (v+c)
    have h₂ := congrFun hcd (v+b)
    change x (v+(c+a)) = z (v+(b+d))
    change x ((v+c)+a) = y ((v+c)+b) at h₁
    change y ((v+b)+c) = z ((v+b)+d) at h₂
    rw [← add_assoc, ← add_assoc]
    exact h₁.trans (by simpa only [add_right_comm v b c] using h₂)

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarGeometry

-- BEGIN COMPLETE MODULE HypersmoothProof.BinaryEncoding
section
                                      
                                   

set_option autoImplicit false

namespace HypersmoothCounterexamples

/-- One additional coordinate codes a natural label below the diagonal marker. -/
def binaryCode {Q : Type*} (x : ℕ × Q → ℕ) (v : ℕ × Q × ℕ) : Bool :=
  if v.2.2 = v.1 then true
  else if v.2.2 < v.1 then decide (x (v.2.2, v.2.1) = v.1-v.2.2-1) else false

theorem continuous_binaryCode {Q : Type*} :
    Continuous (binaryCode : (ℕ × Q → ℕ) → (ℕ × Q × ℕ → Bool)) := by
  apply continuous_pi
  rintro ⟨p, q, t⟩
  by_cases heq : t = p
  · simpa [binaryCode,heq] using
      (continuous_const : Continuous (fun _ : ℕ × Q → ℕ => true))
  · by_cases hlt : t < p
    · simpa [binaryCode,heq,hlt] using
        (continuous_of_discreteTopology (f := fun j : ℕ => decide (j = p-t-1))).comp
          (continuous_apply (t,q) : Continuous (fun x : ℕ × Q → ℕ => x (t,q)))
    · simpa [binaryCode,heq,hlt] using
        (continuous_const : Continuous (fun _ : ℕ × Q → ℕ => false))

@[simp] theorem binaryCode_diag {Q : Type*} (x : ℕ × Q → ℕ) (p : ℕ) (q : Q) :
    binaryCode x (p,q,p) = true := by simp [binaryCode]

theorem le_of_binaryCode_true {Q : Type*} {x : ℕ × Q → ℕ} {p t : ℕ} {q : Q}
    (h : binaryCode x (p,q,t) = true) : t ≤ p := by
  by_contra! hn
  simp [binaryCode,show t ≠ p by omega,show ¬ t < p by omega] at h

theorem binaryCode_at_label {Q : Type*} (x : ℕ × Q → ℕ) (t j : ℕ) (q : Q) :
    binaryCode x (t+j+1,q,t) = true ↔ x (t,q) = j := by
  simp [binaryCode,show t ≠ t+j+1 by omega,show t < t+j+1 by omega,
    show t+j+1-t-1 = j by omega]

theorem binaryCode_forward {Q : Type*} [Add Q] (x : ℕ × Q → ℕ) (a : ℕ × Q) :
    binaryCode (forward a x) = forward (a.1,a.2,a.1) (binaryCode x) := by
  funext v
  rcases v with ⟨p,q,t⟩
  change (if t = p then true else if t < p then
      decide (x (t+a.1,q+a.2) = p-t-1) else false) =
    (if t+a.1 = p+a.1 then true else if t+a.1 < p+a.1 then
      decide (x (t+a.1,q+a.2) = (p+a.1)-(t+a.1)-1) else false)
  simp only [show (t+a.1 = p+a.1) ↔ t = p by omega,
    show (t+a.1 < p+a.1) ↔ t < p by omega,
    show (p+a.1)-(t+a.1)-1 = p-t-1 by omega]

theorem binaryCode_marker_le {Q : Type*} [AddMonoid Q] {x y : ℕ × Q → ℕ}
    {a a' c c' : ℕ} {b b' : Q}
    (h : forward (a,b,c) (binaryCode x) = forward (a',b',c') (binaryCode y)) :
    a+c' ≤ a'+c := by
  let p := c+c'
  let t := p+a-c
  have htc : t+c = p+a := by dsimp [t,p]; omega
  have hpoint := congrFun h (p,0,t)
  change binaryCode x (p+a,0+b,t+c) = binaryCode y (p+a',0+b',t+c') at hpoint
  rw [htc,binaryCode_diag] at hpoint
  have hle := le_of_binaryCode_true hpoint.symm
  omega

theorem binaryCode_reflects_translation {Q : Type*} [AddMonoid Q] {x y : ℕ × Q → ℕ}
    {a a' c c' : ℕ} {b b' : Q}
    (h : forward (a,b,c) (binaryCode x) = forward (a',b',c') (binaryCode y)) :
    a+c' = a'+c ∧ forward (a+c,b) x = forward (a+c',b') y := by
  have hmarker : a+c' = a'+c := le_antisymm (binaryCode_marker_le h) (binaryCode_marker_le h.symm)
  refine ⟨hmarker, funext fun v => ?_⟩
  rcases v with ⟨n,q⟩
  let t := n+a
  let j := x (t+c,q+b)
  let p := t+c+j+1-a
  have hpa : p+a = t+c+j+1 := by dsimp [p,t]; omega
  have hpa' : p+a' = t+c'+j+1 := by omega
  have hpoint := congrFun h (p,q,t)
  change binaryCode x (p+a,q+b,t+c) = binaryCode y (p+a',q+b',t+c') at hpoint
  rw [hpa,hpa',show t+c+j+1 = (t+c)+j+1 by rfl,show t+c'+j+1 = (t+c')+j+1 by rfl] at hpoint
  have hx : binaryCode x ((t+c)+j+1,q+b,t+c) = true :=
    (binaryCode_at_label x (t+c) j (q+b)).mpr rfl
  have hy := (binaryCode_at_label y (t+c') j (q+b')).mp (hpoint.symm.trans hx)
  change x (n+(a+c),q+b) = y (n+(a+c'),q+b')
  rw [← Nat.add_assoc,← Nat.add_assoc]
  exact hy.symm

theorem binaryCode_commonFuture {Q : Type*} [AddMonoid Q] (x y : ℕ × Q → ℕ) :
    CommonFuture x y ↔ CommonFuture (binaryCode x) (binaryCode y) := by
  constructor
  · rintro ⟨a,b,h⟩
    exact ⟨(a.1,a.2,a.1),(b.1,b.2,b.1),
      (binaryCode_forward x a).symm.trans ((congrArg binaryCode h).trans (binaryCode_forward y b))⟩
  · rintro ⟨⟨a,b,c⟩,⟨a',b',c'⟩,h⟩
    exact ⟨(a+c,b),(a+c',b'),(binaryCode_reflects_translation h).2⟩

theorem binaryCode_free {Q : Type*} [AddMonoid Q] {x : ℕ × Q → ℕ}
    (hx : HasFreeTranslates x) : HasFreeTranslates (binaryCode x) := by
  rintro ⟨a,b,c⟩ ⟨a',b',c'⟩ h
  obtain ⟨hmarker, hxshift⟩ := binaryCode_reflects_translation h
  have hpair := hx hxshift
  have hc : c = c' := Nat.add_left_cancel (congrArg Prod.fst hpair)
  have hb : b = b' := congrArg Prod.snd hpair
  have ha : a = a' := by omega
  rw [ha,hb,hc]

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.BinaryEncoding

-- BEGIN COMPLETE MODULE HypersmoothProof.BinaryReduction
section
                                          
                                      

set_option autoImplicit false
noncomputable section

namespace HypersmoothCounterexamples

def tagCode (d : ℕ) : ℕ × Quadrant d → ℕ :=
  Classical.choose (exists_injective_nat (ℕ × Quadrant d))

theorem tagCode_injective (d : ℕ) : Function.Injective (tagCode d) :=
  Classical.choose_spec (exists_injective_nat (ℕ × Quadrant d))

def taggedArray (d : ℕ) (s : Increasing) (v : ℕ × (ℕ × Quadrant d)) : ℕ :=
  tagCode d (planarLabel s (v.1,v.2.1), v.2.2)

theorem continuous_taggedArray (d : ℕ) : Continuous (taggedArray d) := by
  apply continuous_pi
  intro v
  exact (continuous_of_discreteTopology (f := fun n : ℕ => tagCode d (n,v.2.2))).comp
    ((continuous_apply (v.1,v.2.1)).comp continuous_planarLabel)

theorem taggedArray_reflects_translation (d : ℕ) {s t : Increasing}
    {a b : ℕ × (ℕ × Quadrant d)}
    (h : forward a (taggedArray d s) = forward b (taggedArray d t)) :
    a.2.2 = b.2.2 ∧ forward (a.1,a.2.1) (planarLabel s) = forward (b.1,b.2.1) (planarLabel t) := by
  have heq (v : ℕ × ℕ) :
      (planarLabel s (v + (a.1,a.2.1)), (0 : Quadrant d) + a.2.2) =
        (planarLabel t (v + (b.1,b.2.1)), (0 : Quadrant d) + b.2.2) :=
    tagCode_injective d (congrFun h (v.1,v.2,0))
  exact ⟨by simpa using congrArg Prod.snd (heq 0), funext fun v => congrArg Prod.fst (heq v)⟩

theorem taggedArray_commonFuture (d : ℕ) (s t : Increasing) :
    IncreasingRelation s t ↔ CommonFuture (taggedArray d s) (taggedArray d t) := by
  constructor
  · rintro ⟨a,b,h⟩
    refine ⟨(a.1,a.2,0),(b.1,b.2,0),funext fun v => ?_⟩
    change tagCode d (planarLabel s ((v.1,v.2.1)+a), v.2.2+0) =
      tagCode d (planarLabel t ((v.1,v.2.1)+b), v.2.2+0)
    rw [h]
  · rintro ⟨a,b,h⟩
    exact ⟨(a.1,a.2.1),(b.1,b.2.1),congrFun (taggedArray_reflects_translation d h).2⟩

theorem taggedArray_free (d : ℕ) (s : Increasing) : HasFreeTranslates (taggedArray d s) := by
  intro a b h
  obtain ⟨hw,hplane⟩ := taggedArray_reflects_translation d h
  have hp := planarLabel_free s hplane
  have hi : a.1 = b.1 := congrArg (fun v : ℕ × ℕ => v.1) hp
  have hj : a.2.1 = b.2.1 := congrArg (fun v : ℕ × ℕ => v.2) hp
  exact Prod.ext hi (Prod.ext hj hw)

/-- The first three coordinates are the two planar coordinates and the marker coordinate. -/
def binaryCoordinates (d : ℕ) : Quadrant (d+3) ≃+ ℕ × (ℕ × Quadrant d) × ℕ where
  toFun v := (v 0, (Fin.tail v 0, Fin.tail (Fin.tail (Fin.tail v))), Fin.tail (Fin.tail v) 0)
  invFun v := Fin.cons v.1 (Fin.cons v.2.1.1 (Fin.cons v.2.2 v.2.1.2))
  left_inv v := by simp only [Fin.cons_self_tail]
  right_inv v := by simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta]
  map_add' a b := rfl

theorem forward_reindex {I J A : Type*} [Add I] [Add J]
    (e : J ≃+ I) (x : I → A) (a : J) :
    forward a (x ∘ e) = forward (e a) x ∘ e := by
  funext v
  change x (e (v+a)) = x (e v + e a)
  rw [map_add]

theorem commonFuture_reindex {I J A : Type*} [Add I] [Add J]
    (e : J ≃+ I) (x y : I → A) :
    CommonFuture x y ↔ CommonFuture (x ∘ e) (y ∘ e) := by
  constructor
  · rintro ⟨a,b,h⟩
    refine ⟨e.symm a,e.symm b,?_⟩
    rw [forward_reindex,forward_reindex,e.apply_symm_apply,e.apply_symm_apply,h]
  · rintro ⟨a,b,h⟩
    rw [forward_reindex,forward_reindex] at h
    refine ⟨e a,e b,funext fun v => ?_⟩
    obtain ⟨w,rfl⟩ := e.surjective v
    exact congrFun h w

theorem free_reindex {I J A : Type*} [Add I] [Add J]
    (e : J ≃+ I) {x : I → A} (hx : HasFreeTranslates x) : HasFreeTranslates (x ∘ e) := by
  intro a b h
  change forward a (x ∘ e) = forward b (x ∘ e) at h
  rw [forward_reindex,forward_reindex] at h
  apply e.injective
  apply hx
  funext v
  obtain ⟨w,rfl⟩ := e.surjective v
  exact congrFun h w

def binaryReduction (d : ℕ) (s : Increasing) : BinaryFreeSpace (d+3) :=
  ⟨binaryCode (taggedArray d s) ∘ binaryCoordinates d,
    free_reindex _ (binaryCode_free (taggedArray_free d s))⟩

theorem continuous_binaryReduction (d : ℕ) : Continuous (binaryReduction d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact (continuous_apply (binaryCoordinates d v)).comp
    (continuous_binaryCode.comp (continuous_taggedArray d))

theorem binaryReduction_iff (d : ℕ) (s t : Increasing) :
    IncreasingRelation s t ↔ BinaryFreeRelation (d+3) (binaryReduction d s) (binaryReduction d t) :=
  (taggedArray_commonFuture d s t).trans ((binaryCode_commonFuture _ _).trans
    (commonFuture_reindex (binaryCoordinates d) _ _))

theorem increasing_borelReducible_binaryFree (d : ℕ) :
    BorelReducible IncreasingRelation (BinaryFreeRelation (d+3)) :=
  ⟨binaryReduction d, (continuous_binaryReduction d).measurable, binaryReduction_iff d⟩

end HypersmoothCounterexamples

end
end
-- END COMPLETE MODULE HypersmoothProof.BinaryReduction

-- BEGIN COMPLETE MODULE HypersmoothProof.Foundations
section
                                          

set_option autoImplicit false

namespace HypersmoothCounterexamples

theorem Smooth.equivalence {X : Type*} [MeasurableSpace X] {E : X → X → Prop}
    (hE : Smooth E) : Equivalence E := by
  obtain ⟨q, _, hq⟩ := hE
  exact ⟨fun x => (hq x x).mpr rfl, fun h => (hq _ _).mpr ((hq _ _).mp h).symm,
    fun h h' => (hq _ _).mpr (((hq _ _).mp h).trans ((hq _ _).mp h'))⟩

theorem Smooth.pullback {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) {D : Y → Y → Prop} (hD : Smooth D) :
    Smooth (fun x y => D (f x) (f y)) := by
  obtain ⟨q, hq, hclass⟩ := hD
  exact ⟨q ∘ f, hq.comp hf, fun x y => hclass (f x) (f y)⟩

theorem hypersmooth_of_borelReducible {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {E : X → X → Prop} {D : Y → Y → Prop} (hED : BorelReducible E D)
    (hD : Hypersmooth D) : Hypersmooth E := by
  obtain ⟨f, hf, hred⟩ := hED
  obtain ⟨F, hF, hmono, hunion⟩ := hD
  exact ⟨fun n x y => F n (f x) (f y), fun n => (hF n).pullback hf,
    fun n x y => hmono n (f x) (f y), fun x y => (hred x y).trans (hunion (f x) (f y))⟩

theorem BorelReducible.trans {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {E : X → X → Prop} {D : Y → Y → Prop} {F : Z → Z → Prop}
    (hED : BorelReducible E D) (hDF : BorelReducible D F) : BorelReducible E F := by
  obtain ⟨f, hf, hred⟩ := hED
  obtain ⟨g, hg, hred'⟩ := hDF
  exact ⟨g ∘ f, hg.comp hf, fun x y => (hred x y).trans (hred' (f x) (f y))⟩

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.Foundations

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarFibers
section
                                      

set_option autoImplicit false

namespace HypersmoothCounterexamples

open scoped Cardinal

def planarAxis (first : Bool) : ℕ × ℕ := if first then (1,0) else (0,1)

def discardedSite (first : Bool) (n : ℕ) : ℕ × ℕ := if first then (0,n) else (n,0)

def perturbation (first : Bool) (bits : ℕ → Bool) (v : ℕ × ℕ) : ℕ :=
  if first then (if v.1 = 0 then (bits v.2).toNat else 0)
  else (if v.2 = 0 then (bits v.1).toNat else 0)

theorem perturbation_le_one (first : Bool) (bits : ℕ → Bool) (v : ℕ × ℕ) :
    perturbation first bits v ≤ 1 := by
  have h (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  cases first <;> simp [perturbation, apply_ite (· ≤ 1), h]

theorem perturbation_discardedSite (first : Bool) (bits : ℕ → Bool) (n : ℕ) :
    perturbation first bits (discardedSite first n) = (bits n).toNat := by
  cases first <;> simp [perturbation, discardedSite]

theorem perturbation_shift_zero (first : Bool) (bits : ℕ → Bool) (v : ℕ × ℕ) :
    perturbation first bits (v + planarAxis first) = 0 := by
  cases first <;> simp [perturbation, planarAxis, Prod.fst_add, Prod.snd_add]

def spacedEnumeration : Increasing := ⟨fun n => 4*(n+1), fun a b h => by
  change 4*(a+1) < 4*(b+1)
  omega⟩

noncomputable def perturbedEnumeration (first : Bool) (bits : ℕ → Bool) : Increasing :=
  ⟨fun n => 4*(n+1) + perturbation first bits (siteEquiv.symm n), by
    intro n m h
    change 4*(n+1) + perturbation first bits (siteEquiv.symm n) <
      4*(m+1) + perturbation first bits (siteEquiv.symm m)
    have hn := perturbation_le_one first bits (siteEquiv.symm n)
    omega⟩

theorem planarLabel_perturbedEnumeration (first : Bool) (bits : ℕ → Bool) (v : ℕ × ℕ) :
    planarLabel (perturbedEnumeration first bits) v =
      4*(siteIndex v+1) + perturbation first bits v := by
  change 4*(siteIndex v+1) + perturbation first bits (siteEquiv.symm (siteEquiv v)) = _
  rw [Equiv.symm_apply_apply]

noncomputable def perturbedFiber (first : Bool) (bits : ℕ → Bool) :
    {x : PlanarArrays // planarShift (planarAxis first) x =
      planarShift (planarAxis first) (planarPoint spacedEnumeration)} := by
  refine ⟨planarPoint (perturbedEnumeration first bits), ?_⟩
  apply Subtype.ext
  funext v
  change planarLabel (perturbedEnumeration first bits) (v + planarAxis first) =
    4*(siteIndex (v + planarAxis first) + 1)
  rw [planarLabel_perturbedEnumeration, perturbation_shift_zero, Nat.add_zero]

theorem perturbedFiber_injective (first : Bool) : Function.Injective (perturbedFiber first) := by
  intro a b hab
  funext n
  have h := congrArg (fun x => x.val.val (discardedSite first n)) hab
  change planarLabel (perturbedEnumeration first a) (discardedSite first n) =
    planarLabel (perturbedEnumeration first b) (discardedSite first n) at h
  simp only [planarLabel_perturbedEnumeration, perturbation_discardedSite] at h
  have heq := Nat.add_left_cancel h
  cases ha : a n <;> cases hb : b n <;> simp_all

theorem planarAxis_continuum_fiber (first : Bool) : ∃ y : PlanarArrays,
    Cardinal.mk {x : PlanarArrays // planarShift (planarAxis first) x = y} = Cardinal.continuum := by
  refine ⟨planarShift (planarAxis first) (planarPoint spacedEnumeration), le_antisymm ?_ ?_⟩
  · have h := Cardinal.mk_le_of_injective
      (f := fun x : {x : PlanarArrays // planarShift (planarAxis first) x =
        planarShift (planarAxis first) (planarPoint spacedEnumeration)} => (planarRead x.val).val)
      (fun x y h => Subtype.ext (planarHomeomorph.symm.injective (Subtype.ext h)))
    simpa only [Cardinal.mk_arrow, Cardinal.lift_uzero, Cardinal.mk_nat,
      Cardinal.aleph0_power_aleph0] using h
  · have h := Cardinal.mk_le_of_injective (perturbedFiber_injective first)
    simpa only [Cardinal.mk_arrow, Cardinal.lift_uzero, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.continuum] using h

theorem horizontal_continuum_fiber : ∃ y : PlanarArrays,
    Cardinal.mk {x : PlanarArrays // planarShift (1,0) x = y} = Cardinal.continuum :=
  planarAxis_continuum_fiber true

theorem vertical_continuum_fiber : ∃ y : PlanarArrays,
    Cardinal.mk {x : PlanarArrays // planarShift (0,1) x = y} = Cardinal.continuum :=
  planarAxis_continuum_fiber false

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarFibers

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarAssembly
section
                                       
                                   
                                    

set_option autoImplicit false

namespace HypersmoothCounterexamples

theorem increasing_borelReducible_planar : BorelReducible IncreasingRelation PlanarRelation :=
  ⟨planarPoint, continuous_planarPoint.measurable, increasingRelation_iff_planarRelation⟩

theorem planar_counterexample_of_increasing (h : ¬ Hypersmooth IncreasingRelation) :
    Continuous (planarShift (1,0)) ∧ Continuous (planarShift (0,1)) ∧
    Function.Commute (planarShift (1,0)) (planarShift (0,1)) ∧
    ¬ Hypersmooth PlanarRelation ∧
    (∃ y : PlanarArrays,
      Cardinal.mk {x : PlanarArrays // planarShift (1,0) x = y} = Cardinal.continuum) ∧
    (∃ y : PlanarArrays,
      Cardinal.mk {x : PlanarArrays // planarShift (0,1) x = y} = Cardinal.continuum) :=
  ⟨continuous_planarShift _, continuous_planarShift _, planarShift_commute _ _,
    fun hP => h (hypersmooth_of_borelReducible increasing_borelReducible_planar hP),
    horizontal_continuum_fiber, vertical_continuum_fiber⟩

theorem binary_counterexample_of_increasing (h : ¬ Hypersmooth IncreasingRelation) :
    ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ Hypersmooth (BinaryFreeRelation ℓ) := by
  intro ℓ hℓ
  obtain ⟨d,rfl⟩ : ∃ d, ℓ = d+3 := ⟨ℓ-3,(Nat.sub_add_cancel hℓ).symm⟩
  exact fun hb => h (hypersmooth_of_borelReducible (increasing_borelReducible_binaryFree d) hb)

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarAssembly

-- BEGIN COMPLETE MODULE HypersmoothProof.RamseyBasics
section
                                             
                           
                                         
                                   

set_option autoImplicit false

open Set Topology

namespace HypersmoothCounterexamples

/-- The infinite extensions of a finite stem, with all remaining entries in a reservoir. -/
def ramseyNeighborhood (a : Finset ℕ) (L : Set ℕ) : Set Increasing :=
  {x | (a : Set ℕ) ⊆ range x.val ∧ range x.val ⊆ (a : Set ℕ) ∪ L}

def Above (a : Finset ℕ) (L : Set ℕ) : Prop :=
  ∀ i ∈ a, ∀ j ∈ L, i < j

theorem Above.mono {a : Finset ℕ} {L M : Set ℕ} (ha : Above a L) (h : M ⊆ L) :
    Above a M :=
  fun i hi j hj => ha i hi j (h hj)

theorem ramseyNeighborhood_mono (a : Finset ℕ) {L M : Set ℕ} (h : M ⊆ L) :
    ramseyNeighborhood a M ⊆ ramseyNeighborhood a L :=
  fun _ hx => ⟨hx.1, hx.2.trans (union_subset_union_right _ h)⟩

noncomputable def enumerateIncreasing (L : Set ℕ) (hL : L.Infinite) : Increasing :=
  ⟨Nat.nth (· ∈ L), Nat.nth_strictMono hL⟩

@[simp] theorem range_enumerateIncreasing (L : Set ℕ) (hL : L.Infinite) :
    range (enumerateIncreasing L hL).val = L := Nat.range_nth_of_infinite hL

theorem infinite_range_increasing (x : Increasing) : (range x.val).Infinite :=
  infinite_range_of_injective x.property.injective

theorem ramseyNeighborhood_nonempty (a : Finset ℕ) {L : Set ℕ} (hL : L.Infinite) :
    (ramseyNeighborhood a L).Nonempty := by
  let x := enumerateIncreasing ((a : Set ℕ) ∪ L) (hL.mono subset_union_right)
  refine ⟨x, ?_⟩
  change (a : Set ℕ) ⊆ range x.val ∧ range x.val ⊆ (a : Set ℕ) ∪ L
  simp [x, subset_union_left]

theorem tail_infinite {L : Set ℕ} (hL : L.Infinite) (n : ℕ) :
    (L ∩ Ioi n).Infinite := by
  have h := hL.diff (finite_Iic (a := n))
  convert h using 1
  ext k
  simp [not_le]

/-- Finite simultaneous thinning for properties stable under shrinking the reservoir. -/
theorem thin_finset {α : Type*} (A : Finset α) (P : α → Set ℕ → Prop)
    (hmono : ∀ a L M, M ⊆ L → P a L → P a M)
    (L : Set ℕ) (hL : L.Infinite)
    (hthin : ∀ a ∈ A, ∀ R ⊆ L, R.Infinite →
      ∃ M ⊆ R, M.Infinite ∧ P a M) :
    ∃ M ⊆ L, M.Infinite ∧ ∀ a ∈ A, P a M := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨L, subset_rfl, hL, by simp⟩
  | @insert a A _ ih =>
    obtain ⟨R, hRL, hR, hP⟩ := ih (fun b hb => hthin b (Finset.mem_insert_of_mem hb))
    obtain ⟨M, hMR, hM, hPa⟩ := hthin a (Finset.mem_insert_self a A) R hRL hR
    refine ⟨M, hMR.trans hRL, hM, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hPa
    · exact hmono b R M hMR (hP b hb)

structure RamseyStage (L : Set ℕ) where
  stem : Finset ℕ
  pool : Set ℕ
  subset_base : pool ⊆ L
  infinite_pool : pool.Infinite
  stem_below : Above stem pool

/-- Fusion with finitely many selected points and an infinite tail. -/
theorem ramsey_fusion (L : Set ℕ) (hL : L.Infinite)
    (P : ℕ → Finset ℕ → Set ℕ → Prop)
    (hmono : ∀ n a R T, T ⊆ R → P n a R → P n a T)
    (hthin : ∀ n (s : RamseyStage L), ∃ R ⊆ s.pool, R.Infinite ∧ P n s.stem R) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ range m ⊆ L ∧
      ∀ n, P n ((Finset.range n).image m) (m '' Ici n) := by
  classical
  let r (n : ℕ) (s : RamseyStage L) := (hthin n s).choose
  have hr (n : ℕ) (s : RamseyStage L) :
      r n s ⊆ s.pool ∧ (r n s).Infinite ∧ P n s.stem (r n s) :=
    (hthin n s).choose_spec
  let p (n : ℕ) (s : RamseyStage L) := (hr n s).2.1.nonempty.choose
  have hp (n : ℕ) (s : RamseyStage L) : p n s ∈ r n s :=
    (hr n s).2.1.nonempty.choose_spec
  let next (n : ℕ) (s : RamseyStage L) : RamseyStage L :=
    { stem := insert (p n s) s.stem
      pool := r n s ∩ Ioi (p n s)
      subset_base := fun _ hj => s.subset_base ((hr n s).1 hj.1)
      infinite_pool := tail_infinite (hr n s).2.1 _
      stem_below := fun i hi _ hj => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hj.2
        · exact s.stem_below i hi _ ((hr n s).1 hj.1) }
  let S : ℕ → RamseyStage L := fun n => Nat.rec
    { stem := ∅, pool := L, subset_base := subset_rfl, infinite_pool := hL,
      stem_below := by simp [Above] } next n
  let m (n : ℕ) := p n (S n)
  have hpool (n : ℕ) : (S (n + 1)).pool = r n (S n) ∩ Ioi (m n) := rfl
  have hsub (n : ℕ) : (S (n + 1)).pool ⊆ (S n).pool :=
    fun _ hj => (hr n (S n)).1 hj.1
  have hanti : Antitone (fun n => (S n).pool) :=
    antitone_nat_of_succ_le hsub
  have hm (n : ℕ) : m n ∈ (S n).pool := (hr n (S n)).1 (hp n (S n))
  have hstem (n : ℕ) : (S n).stem = (Finset.range n).image m := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      change insert (m n) (S n).stem = _
      rw [ih]
      ext i
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨n, by omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        obtain h | h : j = n ∨ j < n := by omega
        · exact Or.inl (congrArg m h)
        · exact Or.inr ⟨j, h, rfl⟩
  refine ⟨m, ?_, ?_, fun n => ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    have hh := hm (n + 1)
    rw [hpool] at hh
    exact hh.2
  · rintro _ ⟨n, rfl⟩
    exact (S n).subset_base (hm n)
  · rw [← hstem]
    apply hmono _ _ _ _ _ (hr n (S n)).2.2
    rintro _ ⟨j, hj, rfl⟩
    by_cases h : j = n
    · subst j
      exact hp n (S n)
    · have hj' : n + 1 ≤ j := by
        change n ≤ j at hj
        omega
      have hh := hanti hj' (hm j)
      change m j ∈ (S (n + 1)).pool at hh
      rw [hpool] at hh
      exact hh.1

/-- Settle a finite range of tests before each successive fusion point is chosen. -/
theorem ramsey_fusion_all_stems (L : Set ℕ) (hL : L.Infinite) (s : Finset ℕ)
    (Q : ℕ → Finset ℕ → Set ℕ → Prop)
    (hmono : ∀ n a R T, T ⊆ R → Q n a R → Q n a T)
    (hthin : ∀ n a R, R ⊆ L → R.Infinite → Above a R →
      ∃ T ⊆ R, T.Infinite ∧ Q n a T)
    (hs : Above s L) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ range m ⊆ L ∧
      ∀ n (a : Finset ℕ), a ⊆ (Finset.range n).image m → Q n (s ∪ a) (m '' Ici n) := by
  classical
  let P (n : ℕ) (a : Finset ℕ) (R : Set ℕ) := ∀ b ⊆ a, Q n (s ∪ b) R
  apply ramsey_fusion L hL P
  · intro n a R T hRT hR b hb
    exact hmono _ _ _ _ hRT (hR b hb)
  · intro n t
    obtain ⟨T, hTR, hT, hQ⟩ := thin_finset t.stem.powerset (fun b R => Q n (s ∪ b) R)
      (fun b R T h => hmono n (s ∪ b) R T h) t.pool t.infinite_pool (by
        intro b hb R hR hRi
        apply hthin n (s ∪ b) R (hR.trans t.subset_base) hRi
        intro i hi j hj
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hs i hi j (t.subset_base (hR hj))
        · exact t.stem_below i ((Finset.mem_powerset.mp hb) hi) j (hR hj))
    exact ⟨T, hTR, hT, fun b hb => hQ b (Finset.mem_powerset.mpr hb)⟩

theorem image_Ici_infinite {m : ℕ → ℕ} (hm : StrictMono m) (n : ℕ) :
    (m '' Ici n).Infinite := by
  apply (infinite_range_of_injective (hm.comp
    (show StrictMono (fun k : ℕ => n + k) from fun _ _ h => Nat.add_lt_add_left h _)).injective).mono
  rintro _ ⟨i, rfl⟩
  exact ⟨n + i, by simp, rfl⟩

theorem ramsey_invariant_fusion (L : Set ℕ) (hL : L.Infinite)
    (P : Finset ℕ → Set ℕ → Prop) (hinit : P ∅ L)
    (hmono : ∀ a R T, T ⊆ R → P a R → P a T)
    (hstep : ∀ a R, R ⊆ L → R.Infinite → Above a R → P a R →
      ∃ i ∈ R, ∃ T ⊆ R ∩ Ioi i, T.Infinite ∧ P (insert i a) T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ range m ⊆ L ∧
      ∀ n, P ((Finset.range n).image m) (m '' Ici n) := by
  classical
  let State := {s : RamseyStage L // P s.stem s.pool}
  let s0 : State := ⟨{ stem := ∅, pool := L, subset_base := subset_rfl, infinite_pool := hL,
                        stem_below := by simp [Above] }, hinit⟩
  have advance (s : State) := hstep _ _ s.val.subset_base s.val.infinite_pool s.val.stem_below s.prop
  let p (s : State) := (advance s).choose
  have hp (s : State) : p s ∈ s.val.pool :=
    (advance s).choose_spec.1
  let r (s : State) := (advance s).choose_spec.2.choose
  have hr (s : State) : r s ⊆ s.val.pool ∩ Ioi (p s) ∧ (r s).Infinite ∧
      P (insert (p s) s.val.stem) (r s) :=
    (advance s).choose_spec.2.choose_spec
  let next (s : State) : State :=
    ⟨{ stem := insert (p s) s.val.stem
       pool := r s
       subset_base := fun _ hj => s.val.subset_base ((hr s).1 hj).1
       infinite_pool := (hr s).2.1
       stem_below := fun i hi _ hj => by
         rcases Finset.mem_insert.mp hi with rfl | hi
         · exact ((hr s).1 hj).2
         · exact s.val.stem_below i hi _ ((hr s).1 hj).1 }, (hr s).2.2⟩
  let S (n : ℕ) := next^[n] s0
  let m (n : ℕ) := p (S n)
  have hnext (n : ℕ) : S (n + 1) = next (S n) := Function.iterate_succ_apply' _ _ _
  have hpool (n : ℕ) : (S (n + 1)).val.pool = r (S n) := by rw [hnext]
  have hsub (n : ℕ) : (S (n + 1)).val.pool ⊆ (S n).val.pool := by
    rw [hpool]
    exact fun _ hj => ((hr (S n)).1 hj).1
  have hanti : Antitone (fun n => (S n).val.pool) := antitone_nat_of_succ_le hsub
  have hstem (n : ℕ) : (S n).val.stem = (Finset.range n).image m := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hnext]
      change insert (m n) (S n).val.stem = _
      rw [ih]
      ext i
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨n, by omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases heq : j = n
        · exact Or.inl (congrArg m heq)
        · exact Or.inr ⟨j, by omega, rfl⟩
  refine ⟨m, strictMono_nat_of_lt_succ (fun n => ?_), ?_, fun n => ?_⟩
  · have hh := hp (S (n + 1))
    rw [hpool] at hh
    exact ((hr (S n)).1 hh).2
  · rintro _ ⟨n, rfl⟩
    exact (S n).val.subset_base (hp _)
  · rw [← hstem]
    apply hmono _ _ _ _ (S n).prop
    rintro _ ⟨j, hj, rfl⟩
    exact hanti hj (hp (S j))

theorem strictMono_agree_of_range_below {x y : Increasing} {B : ℕ}
    (h : ∀ i < B, i ∈ range x.val ↔ i ∈ range y.val) :
    ∀ k, x.val k < B → y.val k = x.val k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hm := (h (y.val k) (hlt.trans hk)).mpr (mem_range_self k)
      obtain ⟨j, hj⟩ := hm
      have hjk : j < k := x.property.lt_iff_lt.mp (hj ▸ hlt)
      have hey : y.val j = x.val j := ih j hjk ((x.property hjk).trans hk)
      exact (ne_of_lt hjk) (y.property.injective (hey.trans hj))
    · have hm := (h (x.val k) hk).mp (mem_range_self k)
      obtain ⟨j, hj⟩ := hm
      have hjk : j < k := y.property.lt_iff_lt.mp (hj ▸ hlt)
      have hey : y.val j = x.val j := ih j hjk ((x.property hjk).trans hk)
      exact (ne_of_lt hjk) (x.property.injective (hey.symm.trans hj))

/-- A finite cut of a fused reservoir fixes every selected label below that cut. -/
theorem ramsey_neighborhood_cut {s : Finset ℕ} {m : ℕ → ℕ} (hm : StrictMono m)
    {x : Increasing} (hx : x ∈ ramseyNeighborhood s (range m)) (n : ℕ) :
    ∃ a ⊆ (Finset.range n).image m,
      x ∈ ramseyNeighborhood (s ∪ a) (m '' Ici n) ∧
      ∀ y ∈ ramseyNeighborhood (s ∪ a) (m '' Ici n),
        ∀ k, x.val k < m n → y.val k = x.val k := by
  classical
  let a := ((Finset.range n).image m).filter (· ∈ range x.val)
  refine ⟨a, Finset.filter_subset _ _, ?_, ?_⟩
  · constructor
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hx.1 hi
      · exact (Finset.mem_filter.mp hi).2
    · intro i hi
      rcases hx.2 hi with hi | ⟨j, rfl⟩
      · exact Or.inl (Finset.mem_union_left _ hi)
      · by_cases hj : j < n
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩, hi⟩))
        · exact Or.inr ⟨j, Nat.le_of_not_lt hj, rfl⟩
  · intro y hy
    apply strictMono_agree_of_range_below
    intro i hi
    constructor
    · intro hxi
      apply hy.1
      rcases hx.2 hxi with hsi | ⟨j, rfl⟩
      · exact Finset.mem_union_left _ hsi
      · have hj := hm.lt_iff_lt.mp hi
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩, hxi⟩)
    · intro hyi
      rcases hy.2 hyi with hui | ⟨j, hj, rfl⟩
      · rcases Finset.mem_union.mp hui with hsi | hai
        · exact hx.1 hsi
        · exact (Finset.mem_filter.mp hai).2
      · exact ((not_lt_of_ge (hm.monotone hj)) hi).elim

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.RamseyBasics

-- BEGIN COMPLETE MODULE HypersmoothProof.GalvinPrikry
section
                                    

set_option autoImplicit false

open Set Topology

namespace HypersmoothCounterexamples

def CompletelyRamsey (C : Set Increasing) : Prop :=
  ∀ (s : Finset ℕ) (L : Set ℕ), L.Infinite → Above s L →
    ∃ M ⊆ L, M.Infinite ∧
      (ramseyNeighborhood s M ⊆ C ∨ ramseyNeighborhood s M ⊆ Cᶜ)

def Rejects (C : Set Increasing) (s : Finset ℕ) (L : Set ℕ) : Prop :=
  ∀ M ⊆ L, M.Infinite → ¬ ramseyNeighborhood s M ⊆ C

theorem Rejects.mono {C : Set Increasing} {s : Finset ℕ} {L M : Set ℕ}
    (hr : Rejects C s L) (hML : M ⊆ L) : Rejects C s M :=
  fun T hTM => hr T (hTM.trans hML)

theorem resolve_accept_or_reject (C : Set Increasing) (s : Finset ℕ) (L : Set ℕ)
    (hL : L.Infinite) :
    ∃ M ⊆ L, M.Infinite ∧ (ramseyNeighborhood s M ⊆ C ∨ Rejects C s M) := by
  classical
  by_cases hr : Rejects C s L
  · exact ⟨L, subset_rfl, hL, Or.inr hr⟩
  · simp only [Rejects, not_forall, not_not, exists_prop] at hr
    obtain ⟨M, hML, hM, ha⟩ := hr
    exact ⟨M, hML, hM, Or.inl ha⟩

/-- Rejection propagates to each one-point extension on a common thinned tail. -/
theorem reject_successors {C : Set Increasing} {s : Finset ℕ} {L : Set ℕ}
    (hL : L.Infinite) (hr : Rejects C s L) :
    ∃ M ⊆ L, M.Infinite ∧ ∀ i ∈ M, Rejects C (insert i s) (M ∩ Ioi i) := by
  classical
  let P (n : ℕ) (a : Finset ℕ) (R : Set ℕ) :=
    ∀ i ∈ a, ramseyNeighborhood (insert i s) R ⊆ C ∨ Rejects C (insert i s) R
  obtain ⟨m, hm, hmL, hp⟩ := ramsey_fusion L hL P
    (fun n a R T h hR i hi => (hR i hi).imp
      (fun ha => (ramseyNeighborhood_mono _ h).trans ha) (fun hr => hr.mono h)) (by
    intro n t
    exact thin_finset t.stem
      (fun i R => ramseyNeighborhood (insert i s) R ⊆ C ∨ Rejects C (insert i s) R)
      (fun i R T h hh => hh.imp
        (fun ha => (ramseyNeighborhood_mono _ h).trans ha) (fun hr => hr.mono h))
      t.pool t.infinite_pool (fun i _ R _ hR => resolve_accept_or_reject C (insert i s) R hR))
  have hdecision (j : ℕ) :
      ramseyNeighborhood (insert (m j) s) (m '' Ici (j + 1)) ⊆ C ∨
      Rejects C (insert (m j) s) (m '' Ici (j + 1)) :=
    hp (j + 1) (m j) (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩)
  let A := {j | ramseyNeighborhood (insert (m j) s) (m '' Ici (j + 1)) ⊆ C}
  have hA : A.Finite := by
    by_contra hA
    have hAi : A.Infinite := hA
    apply hr (m '' A) (image_subset_range _ _ |>.trans hmL) (hAi.image hm.injective.injOn)
    intro x hx
    have hex : ∃ i, i ∈ range x.val ∧ i ∉ s := by
      by_contra hh
      apply infinite_range_increasing x
      apply (s.finite_toSet).subset
      intro z hz
      by_contra hs
      exact hh ⟨z, hz, hs⟩
    let i := Nat.find hex
    have hi : i ∈ range x.val ∧ i ∉ s := Nat.find_spec hex
    obtain ⟨j, hj, hij⟩ : i ∈ m '' A := (hx.2 hi.1).resolve_left hi.2
    apply hj
    constructor
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvs
      · exact hij ▸ hi.1
      · exact hx.1 hvs
    · intro v hv
      by_cases hs : v ∈ s
      · exact Or.inl (Finset.mem_insert_of_mem hs)
      · obtain ⟨k, hk, rfl⟩ : v ∈ m '' A := (hx.2 hv).resolve_left hs
        have hle : i ≤ m k := Nat.find_min' hex ⟨hv, hs⟩
        rw [← hij] at hle
        by_cases hjk : j = k
        · subst k
          exact Or.inl (Finset.mem_insert_self _ _)
        · have hlt : j < k := by
            have hjle := hm.le_iff_le.mp hle
            omega
          exact Or.inr ⟨k, hlt, rfl⟩
  have hAc : Aᶜ.Infinite := by
    have he : univ \ A = Aᶜ := by ext i; simp
    rw [← he]
    exact infinite_univ.diff hA
  refine ⟨m '' Aᶜ, (image_subset_range _ _).trans hmL,
    hAc.image hm.injective.injOn, ?_⟩
  intro i hi
  obtain ⟨j, hj, rfl⟩ := hi
  have hjr := (hdecision j).resolve_left hj
  apply hjr.mono
  rintro k ⟨⟨l, _, rfl⟩, hlt⟩
  exact ⟨l, hm.lt_iff_lt.mp hlt, rfl⟩

theorem increasing_open_prefix {C : Set Increasing} (hC : IsOpen C) {x : Increasing}
    (hx : x ∈ C) :
    ∃ n : ℕ, ∀ y : Increasing, (∀ k < n, y.val k = x.val k) → y ∈ C := by
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hC
  obtain ⟨W, ⟨z, n, rfl⟩, hxW, hWU⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hx hU
  exact ⟨n, fun y hy => hWU (PiNat.mem_cylinder_iff.mpr (fun k hk =>
    (hy k hk).trans (PiNat.mem_cylinder_iff.mp hxW k hk)))⟩

theorem completelyRamsey_of_isOpen {C : Set Increasing} (hC : IsOpen C) :
    CompletelyRamsey C := by
  classical
  intro s L hL hsL
  obtain ⟨R, hRL, hR, hRdec⟩ := resolve_accept_or_reject C s L hL
  rcases hRdec with hacc | hrej
  · exact ⟨R, hRL, hR, Or.inl hacc⟩
  let P (a : Finset ℕ) (M : Set ℕ) := ∀ b ⊆ a, Rejects C (s ∪ b) M
  obtain ⟨m, hm, hmR, hp⟩ := ramsey_invariant_fusion R hR P
    (by simpa [P] using hrej)
    (fun a M T hM hP b hb => (hP b hb).mono hM) (by
    intro a M hMR hM _ hP
    let Q (b : Finset ℕ) (T : Set ℕ) :=
      ∀ i ∈ T, Rejects C (insert i (s ∪ b)) (T ∩ Ioi i)
    obtain ⟨T, hTM, hT, hQ⟩ := thin_finset a.powerset Q
      (fun b R T h hh i hi => (hh i (h hi)).mono (inter_subset_inter_left _ h))
      M hM (by
        intro b hb T hTM hT
        exact reject_successors hT ((hP b (Finset.mem_powerset.mp hb)).mono hTM))
    obtain ⟨i, hi⟩ := hT.nonempty
    refine ⟨i, hTM hi, T ∩ Ioi i, inter_subset_inter_left _ hTM,
      tail_infinite hT i, fun b hb => ?_⟩
    by_cases hib : i ∈ b
    · have herase : b.erase i ⊆ a := by
        intro j hj
        have hh := Finset.mem_erase.mp hj
        exact (Finset.mem_insert.mp (hb hh.2)).resolve_left hh.1
      have hq := hQ (b.erase i) (Finset.mem_powerset.mpr herase) i hi
      have he : insert i (s ∪ b.erase i) = s ∪ b := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
        by_cases hj : j = i
        · subst j; simp [hib]
        · simp [hj]
      exact he ▸ hq
    · have hba : b ⊆ a := fun j hj =>
        (Finset.mem_insert.mp (hb hj)).resolve_left (fun he => hib (he ▸ hj))
      exact (hP b hba).mono (inter_subset_left.trans hTM))
  refine ⟨range m, hmR.trans hRL, infinite_range_of_injective hm.injective, Or.inr ?_⟩
  intro x hx hxC
  obtain ⟨n, hn⟩ := increasing_open_prefix hC hxC
  have hex : ∃ j, x.val n < m j := by
    have hge : ∀ i, i ≤ m i := by
      intro i
      induction i with
      | zero => omega
      | succ i ih =>
        have hlt : m i < m (i + 1) := hm (Nat.lt_succ_self i)
        change i + 1 ≤ m (i + 1)
        omega
    exact ⟨x.val n + 1, by have := hge (x.val n + 1); omega⟩
  obtain ⟨j, hj⟩ := hex
  obtain ⟨a, ha, hxa, hh⟩ := ramsey_neighborhood_cut hm hx j
  apply hp j a ha (m '' Ici j) subset_rfl (image_Ici_infinite hm j)
  intro y hy
  exact hn y (fun k hk => hh y hy k ((x.property hk).trans hj))

theorem CompletelyRamsey.compl {C : Set Increasing} (hC : CompletelyRamsey C) :
    CompletelyRamsey Cᶜ := by
  intro s L hL hsL
  obtain ⟨M, hML, hM, h⟩ := hC s L hL hsL
  exact ⟨M, hML, hM, by simpa only [compl_compl] using h.symm⟩

theorem increasing_index_le (x : Increasing) (k : ℕ) : k ≤ x.val k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hlt : x.val k < x.val (k + 1) := x.property (Nat.lt_succ_self k)
    change k + 1 ≤ x.val (k + 1)
    omega

theorem range_below_of_prefix {x y : Increasing} {B i : ℕ}
    (h : ∀ k < B, y.val k = x.val k) (hi : i < B) :
    i ∈ range y.val ↔ i ∈ range x.val := by
  constructor
  · rintro ⟨k, hk⟩
    have hkle := increasing_index_le y k
    rw [hk] at hkle
    exact ⟨k, (h k (hkle.trans_lt hi)).symm.trans hk⟩
  · rintro ⟨k, hk⟩
    have hkle := increasing_index_le x k
    rw [hk] at hkle
    exact ⟨k, (h k (hkle.trans_lt hi)).trans hk⟩

theorem ramsey_cut_transfer {s a : Finset ℕ} {m : ℕ → ℕ} {n : ℕ}
    (hm : StrictMono m) (ha : a ⊆ (Finset.range n).image m)
    {x y : Increasing} (hx : x ∈ ramseyNeighborhood (s ∪ a) (m '' Ici n))
    (hy : y ∈ ramseyNeighborhood s (range m))
    (h : ∀ k < m n, y.val k = x.val k) :
    y ∈ ramseyNeighborhood (s ∪ a) (m '' Ici n) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hy.1 hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ha hi)
      apply (range_below_of_prefix h (hm (Finset.mem_range.mp hj))).mpr
      exact hx.1 (Finset.mem_union_right _ hi)
  · intro i hi
    rcases hy.2 hi with hsi | ⟨j, rfl⟩
    · exact Or.inl (Finset.mem_union_left _ hsi)
    · by_cases hj : j < n
      · rcases hx.2 ((range_below_of_prefix h (hm hj)).mp hi) with hs | ⟨k, hk, he⟩
        · exact Or.inl hs
        · have hh : k = j := hm.injective he
          subst k
          exact (not_lt_of_ge hk hj).elim
      · exact Or.inr ⟨j, Nat.le_of_not_lt hj, rfl⟩

/-- One fusion makes each of countably many completely Ramsey sets depend on a finite cut. -/
theorem ramsey_read_sets (C : ℕ → Set Increasing) (hC : ∀ n, CompletelyRamsey (C n))
    (s : Finset ℕ) (L : Set ℕ) (hL : L.Infinite) (hs : Above s L) :
    ∃ M ⊆ L, M.Infinite ∧
      ∀ n, ∃ len : ℕ, ∀ x ∈ ramseyNeighborhood s M, ∀ y ∈ ramseyNeighborhood s M,
        (∀ k < len, y.val k = x.val k) → (x ∈ C n ↔ y ∈ C n) := by
  let Q (n : ℕ) (a : Finset ℕ) (R : Set ℕ) :=
    ramseyNeighborhood a R ⊆ C n ∨ ramseyNeighborhood a R ⊆ (C n)ᶜ
  obtain ⟨m, hm, hmL, hp⟩ := ramsey_fusion_all_stems L hL s Q
    (fun n a R T h hh => hh.imp (fun hc => (ramseyNeighborhood_mono _ h).trans hc)
      (fun hc => (ramseyNeighborhood_mono _ h).trans hc))
    (fun n a R _ hR ha => hC n a R hR ha) hs
  refine ⟨range m, hmL, infinite_range_of_injective hm.injective, fun n => ⟨m n, ?_⟩⟩
  intro x hx y hy h
  obtain ⟨a, ha, hxa, _⟩ := ramsey_neighborhood_cut hm hx n
  have hya := ramsey_cut_transfer hm ha hxa hy h
  rcases hp n a ha with hpos | hneg
  · exact iff_of_true (hpos hxa) (hpos hya)
  · exact iff_of_false (hneg hxa) (hneg hya)

theorem subtype_isOpen_of_prefix {N : Set Increasing} {A : Set N}
    (h : ∀ x ∈ A, ∃ n : ℕ, ∀ y : N, (∀ k < n, y.val.val k = x.val.val k) → y ∈ A) :
    IsOpen A := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨n, hn⟩ := h x hx
  let base : N → (ℕ → ℕ) := fun y => y.val.val
  have hb : Continuous base := continuous_subtype_val.comp continuous_subtype_val
  have ho : IsOpen (base ⁻¹' PiNat.cylinder x.val.val n) :=
    (PiNat.isOpen_cylinder (fun _ => ℕ) _ _).preimage hb
  apply Filter.mem_of_superset (ho.mem_nhds (PiNat.self_mem_cylinder _ _))
  intro y hy
  exact hn y (PiNat.mem_cylinder_iff.mp hy)

theorem completelyRamsey_iUnion (C : ℕ → Set Increasing)
    (hC : ∀ n, CompletelyRamsey (C n)) : CompletelyRamsey (⋃ n, C n) := by
  intro s L hL hs
  obtain ⟨M, hML, hM, hm⟩ := ramsey_read_sets C hC s L hL hs
  let N := ramseyNeighborhood s M
  let A : Set N := {x | x.val ∈ ⋃ n, C n}
  have hAo : IsOpen A := by
    apply subtype_isOpen_of_prefix
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := hm i
    exact ⟨n, fun y hy => Set.mem_iUnion.mpr ⟨i, (hn x x.prop y y.prop hy).mp hi⟩⟩
  obtain ⟨U, hU, he⟩ := isOpen_induced_iff.mp hAo
  obtain ⟨M', hM'M, hM', hdec⟩ := completelyRamsey_of_isOpen hU s M hM (hs.mono hML)
  refine ⟨M', hM'M.trans hML, hM', hdec.imp ?_ ?_⟩
  · intro hh x hx
    let y : N := ⟨x, ramseyNeighborhood_mono s hM'M hx⟩
    have hy : y ∈ Subtype.val ⁻¹' U := hh hx
    simpa only [he] using hy
  · intro hh x hx hxC
    let y : N := ⟨x, ramseyNeighborhood_mono s hM'M hx⟩
    have hy : y ∈ A := hxC
    rw [← he] at hy
    exact hh hx hy

/-- The Galvin–Prikry theorem for the space of increasing natural sequences. -/
theorem galvinPrikry {C : Set Increasing} (hC : MeasurableSet C) :
    CompletelyRamsey C := by
  rw [BorelSpace.measurable_eq (α := Increasing)] at hC
  exact MeasurableSpace.generateFrom_induction {U : Set Increasing | IsOpen U}
    (fun S _ => CompletelyRamsey S)
    (fun _ hU _ => completelyRamsey_of_isOpen hU)
    (completelyRamsey_of_isOpen isOpen_empty)
    (fun _ _ h => h.compl)
    (fun S _ h => completelyRamsey_iUnion S h) C hC

def RamseyCone (L : Set ℕ) : Set Increasing := {x | range x.val ⊆ L}

theorem isClosed_ramseyCone (L : Set ℕ) : IsClosed (RamseyCone L) := by
  have he : RamseyCone L = ⋂ k : ℕ, (fun x : Increasing => x.val k) ⁻¹' L := by
    ext x
    simp [RamseyCone, range_subset_iff]
  rw [he]
  exact isClosed_iInter fun k =>
    (isClosed_discrete _).preimage ((continuous_apply k).comp continuous_subtype_val)

theorem ramseyNeighborhood_empty (L : Set ℕ) :
    ramseyNeighborhood ∅ L = RamseyCone L := by
  ext x
  simp [RamseyCone, ramseyNeighborhood]

theorem ramsey_read_borel_sets {J : Type*} [Countable J] (C : J → Set Increasing)
    (hC : ∀ i, MeasurableSet (C i)) (L : Set ℕ) (hL : L.Infinite) :
    ∃ M ⊆ L, M.Infinite ∧
      ∀ i, ∃ len : ℕ, ∀ x ∈ RamseyCone M, ∀ y ∈ RamseyCone M,
        (∀ k < len, y.val k = x.val k) → (x ∈ C i ↔ y ∈ C i) := by
  cases isEmpty_or_nonempty J with
  | inl h => exact ⟨L, subset_rfl, hL, fun i => (h.false i).elim⟩
  | inr h =>
    obtain ⟨f, hf⟩ := exists_surjective_nat J
    obtain ⟨M, hML, hM, he⟩ := ramsey_read_sets (C ∘ f)
      (fun i => galvinPrikry (hC (f i))) ∅ L hL (by simp [Above])
    rw [ramseyNeighborhood_empty] at he
    exact ⟨M, hML, hM, fun i => by obtain ⟨j, rfl⟩ := hf i; exact he j⟩

theorem continuous_of_prefix_locally {Y : Type*} [TopologicalSpace Y] {N : Set Increasing}
    (f : N → Y)
    (hf : ∀ x, ∃ n : ℕ, ∀ y : N, (∀ k < n, y.val.val k = x.val.val k) → f y = f x) :
    Continuous f := by
  apply continuous_def.mpr
  intro A _
  apply subtype_isOpen_of_prefix
  intro x hx
  obtain ⟨n, hn⟩ := hf x
  exact ⟨n, fun y hy => show f y ∈ A from hn y hy ▸ hx⟩

/-- Borel Cantor-valued maps are simultaneously continuous on a closed Ramsey cone. -/
theorem exists_continuousOn_ramseyCone (q : ℕ → Increasing → ℕ → Bool)
    (hq : ∀ n, Measurable (q n)) (L : Set ℕ) (hL : L.Infinite) :
    ∃ M ⊆ L, M.Infinite ∧ ∀ n, Continuous (fun x : RamseyCone M => q n x.val) := by
  let C : ℕ × ℕ → Set Increasing := fun ik => {x | q ik.1 x ik.2 = true}
  have hc (ik : ℕ × ℕ) : MeasurableSet (C ik) :=
    ((measurable_pi_apply ik.2).comp (hq ik.1)) (measurableSet_singleton true)
  obtain ⟨M, hML, hM, hcut⟩ := ramsey_read_borel_sets C hc L hL
  refine ⟨M, hML, hM, fun n => continuous_pi fun k => ?_⟩
  apply continuous_of_prefix_locally
  intro x
  obtain ⟨len, hlen⟩ := hcut (n, k)
  refine ⟨len, fun y hy => ?_⟩
  have he : q n x.val k = true ↔ q n y.val k = true := hlen x x.prop y y.prop hy
  cases hx : q n x.val k <;> cases hy : q n y.val k <;> simp_all

theorem ramsey_read_relative_sets {J : Type*} [Countable J] (R : Set ℕ) (hR : R.Infinite)
    (C : J → Set (RamseyCone R)) (hC : ∀ i, MeasurableSet (C i)) :
    ∃ M ⊆ R, M.Infinite ∧
      ∀ i, ∃ len : ℕ, ∀ x y : RamseyCone R, x.val ∈ RamseyCone M →
        y.val ∈ RamseyCone M → (∀ k < len, y.val.val k = x.val.val k) →
        (x ∈ C i ↔ y ∈ C i) := by
  let D (i : J) : Set Increasing := Subtype.val '' C i
  have hd (i : J) : MeasurableSet (D i) :=
    (MeasurableEmbedding.subtype_coe (isClosed_ramseyCone R).measurableSet).measurableSet_image.mpr
      (hC i)
  obtain ⟨M, hMR, hM, h⟩ := ramsey_read_borel_sets D hd R hR
  refine ⟨M, hMR, hM, fun i => ?_⟩
  obtain ⟨len, hlen⟩ := h i
  refine ⟨len, fun x y hx hy hpre => ?_⟩
  have htest := hlen x hx y hy hpre
  simpa only [D, Subtype.coe_injective.mem_set_image] using htest

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.GalvinPrikry

-- BEGIN COMPLETE MODULE HypersmoothProof.Overlap
section
                              
                                
                              
                             
                                                    
                                     
                                          
                                        

set_option autoImplicit false

namespace HypersmoothCounterexamples

abbrev IncreasingWord (I : Finset ℕ) (r : ℕ) :=
  {u : Fin r → ℕ // StrictMono u ∧ ∀ i, u i ∈ I}

def Overlap {I : Finset ℕ} {r : ℕ} (u v : IncreasingWord I r) : Prop :=
  (∀ i j : Fin r, i.val + 1 = j.val → u.val j = v.val i) ∧
  (∀ i : Fin r, i.val + 1 = r → u.val i < v.val i)

namespace OverlapProof

def oriented {V : Type*} (R : V → V → Prop) (b : Bool) (x y : V) : Prop :=
  if b then R x y else R y x

inductive Walk {V : Type*} (R : V → V → Prop) : List Bool → V → V → Prop
  | nil (x : V) : Walk R [] x x
  | cons {b : Bool} {s : List Bool} {x y z : V} :
      oriented R b x y → Walk R s y z → Walk R (b :: s) x z

variable {V W : Type*} {R : V → V → Prop} {S : W → W → Prop}

theorem Walk.append {s t : List Bool} {x y z : V} (h : Walk R s x y)
    (k : Walk R t y z) : Walk R (s ++ t) x z := by
  induction h with
  | nil => exact k
  | cons he _ ih => exact .cons he (ih k)

def inverse (s : List Bool) : List Bool := s.reverse.map (! ·)

theorem Walk.reverse {s : List Bool} {x y : V} (h : Walk R s x y) :
    Walk R (inverse s) y x := by
  induction h with
  | nil => exact .nil _
  | @cons b s x y z he h ih =>
    simp only [inverse, List.reverse_cons, List.map_append, List.map_singleton]
    apply ih.append
    exact .cons (by cases b <;> simpa [oriented] using he) (.nil x)

theorem Walk.map {s : List Bool} {x y : V} (h : Walk R s x y) (f : V → W)
    (hf : ∀ a b, R a b → S (f a) (f b)) : Walk S s (f x) (f y) := by
  induction h with
  | nil => exact .nil _
  | @cons b s x y z he h ih =>
    apply Walk.cons _ ih
    cases b <;> exact hf _ _ he

theorem Walk.finiteSupport {s : List Bool} {x y : V} (h : Walk R s x y) :
    ∃ (P : Finset V) (hx : x ∈ P) (hy : y ∈ P),
      Walk (fun a b : P => R a.val b.val) s ⟨x,hx⟩ ⟨y,hy⟩ := by
  classical
  induction h with
  | nil x =>
    exact ⟨{x},by simp,by simp,.nil _⟩
  | @cons b s x y z he h ih =>
    obtain ⟨P,hy,hz,hP⟩ := ih
    let Q := insert x P
    have incl : P ⊆ Q := Finset.subset_insert x P
    let f : P → Q := fun u => ⟨u.val,incl u.property⟩
    have hx : x ∈ Q := Finset.mem_insert_self x P
    have he' : oriented (fun a b : Q => R a.val b.val) b ⟨x,hx⟩ (f ⟨y,hy⟩) := by
      cases b <;> exact he
    exact ⟨Q,hx,incl hz,.cons he' (hP.map f (fun _ _ h => h))⟩

theorem Walk.eq_of_nil {x y : V} (h : Walk R [] x y) : x = y := by
  cases h
  rfl

theorem Walk.exists_middle {b : Bool} {s : List Bool} {x y : V}
    (h : Walk R (b :: s) x y) : ∃ z, oriented R b x z ∧ Walk R s z y := by
  cases h with
  | cons he hw => exact ⟨_,he,hw⟩

def copies (s : List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => s ++ copies s n

theorem Walk.repeat {s : List Bool} {x : V} (h : Walk R s x x) (n : ℕ) :
    Walk R (copies s n) x x := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact h.append ih

def step (b : Bool) : ℤ := if b then 1 else -1
def total (s : List Bool) : ℤ := (s.map step).sum

theorem total_append (s t : List Bool) : total (s ++ t) = total s + total t := by
  simp [total, List.sum_append]

theorem total_inverse (s : List Bool) : total (inverse s) = -total s := by
  induction s with
  | nil => simp [total, inverse]
  | cons b s ih =>
    have he : inverse (b :: s) = inverse s ++ [!b] := by simp [inverse]
    rw [he, total_append, ih]
    cases b <;> simp [total,step]

theorem total_copies (s : List Bool) (n : ℕ) : total (copies s n) = n * total s := by
  induction n with
  | zero => simp [copies,total]
  | succ n ih => simp [copies,total_append,ih,Int.natCast_succ,Int.add_mul,Int.add_comm]

theorem total_mod_two (s : List Bool) : total s % 2 = (s.length : ℤ) % 2 := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    change (step b + total s) % 2 = ((s.length : ℤ) + 1) % 2
    cases b <;> simp [step] <;> omega

def extendSigns (s : List Bool) (r : ℕ) : List Bool :=
  copies s (r+1) ++ copies (inverse s) r

theorem total_extendSigns (s : List Bool) (r : ℕ) (hs : total s = 1) :
    total (extendSigns s r) = 1 := by
  simp [extendSigns,total_append,total_copies,total_inverse,hs]

def schedule (r : ℕ → ℕ) : ℕ → List Bool
  | 0 => [true]
  | n+1 => extendSigns (schedule r n) (r n)

theorem total_schedule (r : ℕ → ℕ) (n : ℕ) : total (schedule r n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact total_extendSigns _ _ ih

theorem Walk.extend {s : List Bool} {x : V} (h : Walk R s x x) (r : ℕ) :
    Walk R (extendSigns s r) x x :=
  (h.repeat (r+1)).append (h.reverse.repeat r)

theorem Walk.later (r : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) {x : V}
    (h : Walk R (schedule r j) x x) : Walk R (schedule r m) x x := by
  induction hjm with
  | refl => exact h
  | @step n _ ih => exact ih.extend (r n)

abbrev IntWord (r : ℕ) := {u : Fin r → ℤ // StrictMono u}

def intOverlap {r : ℕ} (u v : IntWord r) : Prop :=
  (∀ i j : Fin r, i.val + 1 = j.val → u.val j = v.val i) ∧
  (∀ i : Fin r, i.val + 1 = r → u.val i < v.val i)

def window {r : ℕ} (L : ℤ → ℤ) (hL : StrictMono L) (p : ℤ) : IntWord r :=
  ⟨fun i => L (p + i.val), fun i j hij => hL (by
    have hi : i.val < j.val := hij
    omega)⟩

theorem window_succ {r : ℕ} (L : ℤ → ℤ) (hL : StrictMono L) (p : ℤ) :
    intOverlap (window (r := r) L hL p) (window L hL (p+1)) := by
  constructor
  · intro i j hij
    change L (p + j.val) = L (p + 1 + i.val)
    congr 1
    omega
  · intro i _
    apply hL
    change p + (i.val : ℤ) < p + 1 + i.val
    omega

theorem window_walk {r : ℕ} (L : ℤ → ℤ) (hL : StrictMono L) (s : List Bool) (p : ℤ) :
    Walk (intOverlap (r := r)) s (window L hL p) (window L hL (p + total s)) := by
  induction s generalizing p with
  | nil => simpa [total] using Walk.nil (R := intOverlap) (window (r := r) L hL p)
  | cons b s ih =>
    have he : oriented (intOverlap (r := r)) b (window L hL p) (window L hL (p+step b)) := by
      cases b
      · simpa [oriented,step] using (window_succ (r := r) L hL (p-1))
      · simpa [oriented,step] using (window_succ (r := r) L hL p)
    have hsum : p + step b + total s = p + total (b :: s) := by simp [total]; omega
    rw [← hsum]
    exact Walk.cons he (ih (p+step b))

def shiftedLetters (r : ℕ) (z : ℤ) : ℤ := if z < (r : ℤ)+1 then z-1 else z

theorem strictMono_shiftedLetters (r : ℕ) : StrictMono (shiftedLetters r) := by
  intro x y hxy
  unfold shiftedLetters
  split <;> split <;> omega

theorem new_int_walk (s : List Bool) (r : ℕ) (hs : total s = 1) :
    ∃ x : IntWord r, Walk intOverlap (extendSigns s r) x x := by
  let start : IntWord r := window id strictMono_id 0
  let L := shiftedLetters r
  let hL := strictMono_shiftedLetters r
  have hp : (0 : ℤ) + total (copies s (r+1)) = (r : ℤ)+1 := by simp [total_copies,hs]
  have hq : (r : ℤ)+1 + total (copies (inverse s) r) = 1 := by
    simp [total_copies,total_inverse,hs]
  have switch : window (r := r) id strictMono_id ((r:ℤ)+1) = window L hL ((r:ℤ)+1) := by
    apply Subtype.ext
    funext i
    change (r : ℤ)+1 + i.val = shiftedLetters r ((r : ℤ)+1+i.val)
    unfold shiftedLetters
    rw [if_neg (by omega)]
  have finish : window (r := r) L hL 1 = start := by
    apply Subtype.ext
    funext i
    change shiftedLetters r (1+i.val) = (0:ℤ)+i.val
    unfold shiftedLetters
    rw [if_pos (by have := i.isLt; omega)]
    omega
  have h₁ := window_walk (r := r) id strictMono_id (copies s (r+1)) 0
  have h₂ := window_walk (r := r) L hL (copies (inverse s) r) ((r:ℤ)+1)
  rw [hp,switch] at h₁
  rw [hq,finish] at h₂
  exact ⟨start,h₁.append h₂⟩

theorem increasing_in_reservoir (L : Set ℕ) (hL : L.Infinite) (bound : ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, e n ∈ L ∧ bound < e n := by
  classical
  choose next hn hlt using hL.exists_gt
  let e : ℕ → ℕ := fun n => (next^[n+1]) bound
  have estep (n : ℕ) : e (n+1) = next (e n) := by simp [e, Function.iterate_succ_apply']
  have hmono : StrictMono e := strictMono_nat_of_lt_succ (fun n => by rw [estep]; exact hlt _)
  refine ⟨e,hmono,fun n => ⟨?_,(hlt bound).trans_le (hmono.monotone (Nat.zero_le n))⟩⟩
  simpa [e, Function.iterate_succ_apply'] using hn ((next^[n]) bound)

theorem new_finite_walk (s : List Bool) (r bound : ℕ) (hs : total s = 1) (hr : 0 < r)
    (L : Set ℕ) (hL : L.Infinite) :
    ∃ I : Finset ℕ, (∀ i ∈ I, i ∈ L ∧ bound < i) ∧
      ∃ x : IncreasingWord I r, Walk Overlap (extendSigns s r) x x := by
  classical
  obtain ⟨start,h⟩ := new_int_walk s r hs
  obtain ⟨P,hx,_,hw⟩ := h.finiteSupport
  let letters : Finset ℤ := P.biUnion (fun a => Finset.univ.image a.val)
  have in_letters (a : P) (i : Fin r) : a.val.val i ∈ letters :=
    Finset.mem_biUnion.mpr ⟨a.val,a.property,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hletters : letters.Nonempty := ⟨start.val ⟨0,hr⟩,in_letters ⟨start,hx⟩ ⟨0,hr⟩⟩
  let lo := letters.min' hletters
  obtain ⟨e,he,hE⟩ := increasing_in_reservoir L hL bound
  let φ (z : ℤ) := e (z-lo).toNat
  let I := letters.image φ
  have hφ {z w : ℤ} (hz : z ∈ letters) (hlt : z < w) : φ z < φ w := by
    have hlo : lo ≤ z := letters.min'_le z hz
    apply he
    omega
  let f (a : P) : IncreasingWord I r :=
    ⟨fun i => φ (a.val.val i),fun i j hij => hφ (in_letters a i) (a.val.property hij),
      fun i => Finset.mem_image_of_mem _ (in_letters a i)⟩
  refine ⟨I, ?_,f ⟨start,hx⟩,hw.map f ?_⟩
  · intro i hi
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hi
    exact hE _
  · intro a b hab
    exact ⟨fun i j hij => congrArg φ (hab.1 i j hij),
      fun i hi => hφ (in_letters a i) (hab.2 i hi)⟩

theorem exists_factor_walks (r : ℕ → ℕ) (hr : ∀ j, 0 < r j) (L : Set ℕ) (hL : L.Infinite) :
    ∃ I : ℕ → Finset ℕ,
      (∀ j, (I j : Set ℕ) ⊆ L) ∧
      (∀ j k, j < k → ∀ i ∈ I j, ∀ i' ∈ I k, i < i') ∧
      ∀ j, ∃ x : IncreasingWord (I j) (r j), Walk Overlap (schedule r (j+1)) x x := by
  classical
  have choices (j b : ℕ) := new_finite_walk (schedule r j) (r j) b (total_schedule r j) (hr j) L hL
  choose A hA roots walks using choices
  have ane (j b : ℕ) : (A j b).Nonempty :=
    ⟨(roots j b).val ⟨0,hr j⟩,(roots j b).property.2 ⟨0,hr j⟩⟩
  let bound : ℕ → ℕ := Nat.rec 0 (fun j b => (A j b).max' (ane j b))
  let I j := A j (bound j)
  have hupper {j i : ℕ} (h : i ∈ I j) : i ≤ bound (j+1) := (I j).le_max' i h
  have hbound (j : ℕ) : bound j < bound (j+1) :=
    (hA j (bound j) _ ((I j).max'_mem (ane j (bound j)))).2
  refine ⟨I,fun j _ hi => (hA j (bound j) _ hi).1, ?_,fun j => ⟨roots j (bound j),walks j (bound j)⟩⟩
  intro j k hjk i hi i' hi'
  exact ((hupper hi).trans ((strictMono_nat_of_lt_succ hbound).monotone hjk)).trans_lt
    (hA k (bound k) _ hi').2

theorem Walk.pi {J : Type*} {X : J → Type*} {R : ∀ j, X j → X j → Prop}
    {s : List Bool} {x y : ∀ j, X j} (h : ∀ j, Walk (R j) s (x j) (y j)) :
    Walk (fun a b => ∀ j, R j (a j) (b j)) s x y := by
  classical
  induction s generalizing x y with
  | nil =>
    have hxy : x = y := funext (fun j => (h j).eq_of_nil)
    subst y
    exact .nil _
  | cons b s ih =>
    have h' (j : J) : ∃ z : X j, oriented (R j) b (x j) z ∧ Walk (R j) s z (y j) :=
      (h j).exists_middle
    choose z he hw using h'
    apply Walk.cons ?_ (ih hw)
    cases b <;> exact he

theorem Walk.color_mod {s : List Bool} {x y : V} (walk : Walk R s x y)
    (c : V → Bool) (h : ∀ a b, R a b → c a ≠ c b) :
    ((if c x then (1 : ℤ) else 0) + (s.length : ℤ)) % 2 =
      (if c y then (1 : ℤ) else 0) % 2 := by
  induction walk with
  | nil => simp
  | @cons b s x y z he hw ih =>
    have hd : c x ≠ c y := by
      cases b
      · exact (h _ _ he).symm
      · exact h _ _ he
    change ((if c x then (1 : ℤ) else 0) + ((s.length : ℤ)+1)) % 2 = _
    change ((if c y then (1 : ℤ) else 0) + (s.length : ℤ)) % 2 = _ at ih
    cases hx : c x <;> cases hy : c y <;> simp [hx,hy] at hd ih ⊢ <;> omega

theorem Walk.monochromatic {s : List Bool} {x : V} (walk : Walk R s x x)
    (hs : total s = 1) (c : V → Bool) : ∃ a b, R a b ∧ c a = c b := by
  classical
  by_contra! h
  have hpar := total_mod_two s
  rw [hs] at hpar
  have hh := walk.color_mod c h
  change ((if c x then (1 : ℤ) else 0) + (s.length : ℤ)) % 2 = _ at hh
  cases hx : c x <;> simp [hx] at hh <;> omega

end OverlapProof

open OverlapProof in
/-- Ordered finite alphabets with monochromatic synchronized overlap edges. -/
theorem exists_overlap_alphabets (r : ℕ → ℕ) (hr : ∀ j, 0 < r j) (L : Set ℕ)
    (hL : L.Infinite) :
    ∃ I : ℕ → Finset ℕ,
      (∀ j, (I j : Set ℕ) ⊆ L) ∧
      (∀ j k, j < k → ∀ i ∈ I j, ∀ i' ∈ I k, i < i') ∧
      (∀ j, Nonempty (IncreasingWord (I j) (r j))) ∧
      ∀ m : ℕ, 0 < m → ∀ c : (∀ j : Fin m, IncreasingWord (I j.val) (r j.val)) → Bool,
        ∃ u v, (∀ j, Overlap (u j) (v j)) ∧ c u = c v := by
  classical
  obtain ⟨I,hL,horder,hwalks⟩ := exists_factor_walks r hr L hL
  choose x hx using hwalks
  refine ⟨I,hL,horder,fun j => ⟨x j⟩,fun m _ c => ?_⟩
  have h (j : Fin m) := (hx j.val).later r (Nat.succ_le_of_lt j.isLt)
  exact (Walk.pi h).monochromatic (total_schedule r m) c

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.Overlap

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarBlocks
section
                                    
                               
                                      
                                           

set_option autoImplicit false

open Set Topology

namespace HypersmoothCounterexamples

theorem siteIndex_lt_diagonalStart_iff (v : ℕ × ℕ) (n : ℕ) :
    siteIndex v < diagonalStart n ↔ v.1 + v.2 < n := by
  rw [← show siteIndex (n,0) = diagonalStart n by simp [siteIndex], siteIndex_lt_iff]
  simp

theorem siteIndex_siteEquiv_symm (k : ℕ) : siteIndex (siteEquiv.symm k) = k :=
  siteEquiv.apply_symm_apply k

def dropIncreasing (n : ℕ) (x : Increasing) : Increasing :=
  ⟨fun k => x.val (n+k), fun _ _ h => x.property (Nat.add_lt_add_left h _)⟩

def prependIncreasing (n : ℕ) (x y : Increasing)
    (h : ∀ i < n, ∀ j, x.val i < y.val j) : Increasing :=
  ⟨fun k => if k < n then x.val k else y.val (k-n), by
    intro i j hij
    by_cases hj : j < n
    · simp [if_pos (hij.trans hj), if_pos hj, x.property hij]
    · by_cases hi : i < n
      · simpa [hi, hj] using h i hi (j-n)
      · simp only [if_neg hi, if_neg hj]
        exact y.property (show i-n < j-n by omega)⟩

theorem prependIncreasing_prefix (n : ℕ) (x y : Increasing) (h : ∀ i < n, ∀ j, x.val i < y.val j)
    (k : ℕ) (hk : k < n) : (prependIncreasing n x y h).val k = x.val k := by
  simp [prependIncreasing, hk]

theorem prependIncreasing_tail (n : ℕ) (x y : Increasing) (h : ∀ i < n, ∀ j, x.val i < y.val j)
    (k : ℕ) : (prependIncreasing n x y h).val (n+k) = y.val k := by
  simp [prependIncreasing]

theorem prependIncreasing_continuous (n : ℕ) (x : Increasing) {L : Set ℕ}
    (h : ∀ i < n, ∀ j ∈ L, x.val i < j) :
    Continuous (fun y : RamseyCone L => prependIncreasing n x y.val
      (fun i hi j => h i hi _ (y.property (mem_range_self j)))) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  by_cases hk : k < n
  · simpa [prependIncreasing, hk] using (continuous_const : Continuous (fun _ : RamseyCone L => x.val k))
  · simpa [prependIncreasing, hk] using
      ((continuous_apply (k-n)).comp (continuous_subtype_val.comp continuous_subtype_val) :
        Continuous (fun y : RamseyCone L => y.val.val (k-n)))

theorem prependIncreasing_cone {L R : Set ℕ} (n : ℕ) (x : RamseyCone L)
    (hRL : R ⊆ L) (h : ∀ i < n, ∀ j ∈ R, x.val.val i < j) :
    ∃ f : RamseyCone R → RamseyCone L, Continuous f ∧
      ∀ y, (f y).val = prependIncreasing n x.val y.val
        (fun i hi j => h i hi _ (y.property (mem_range_self j))) := by
  let g (y : RamseyCone R) :=
    prependIncreasing n x.val y.val (fun i hi j => h i hi _ (y.property (mem_range_self j)))
  have hg (y : RamseyCone R) : g y ∈ RamseyCone L := by
    rintro _ ⟨k, rfl⟩
    by_cases hk : k < n
    · simpa [g, prependIncreasing, hk] using x.property (mem_range_self k)
    · simpa [g, prependIncreasing, hk] using hRL (y.property (mem_range_self (k-n)))
  exact ⟨fun y => ⟨g y, hg y⟩, (prependIncreasing_continuous n x.val h).subtype_mk _,
    fun _ => rfl⟩

theorem prepend_drop_of_prefix (n : ℕ) (x y : Increasing)
    (h : ∀ i < n, x.val i = y.val i) :
    prependIncreasing n x (dropIncreasing n y)
      (fun i hi j => (h i hi) ▸ y.property (show i < n+j by omega)) = y := by
  apply Subtype.ext
  funext k
  by_cases hk : k < n
  · exact (prependIncreasing_prefix _ _ _ _ _ hk).trans (h k hk)
  · have he : n + (k-n) = k := by omega
    simp [prependIncreasing, dropIncreasing, hk, he]

section BlockProduct

variable (n : ℕ) (I : ℕ → Finset ℕ)

/-- The increasing word of the jth shell after the stem. -/
abbrev BlockWord (j : ℕ) := IncreasingWord (I j) (n+j+1)

abbrev BlockProduct := ∀ j : ℕ, BlockWord n I j

instance (j : ℕ) : Finite (BlockWord n I j) := by
  let f (u : BlockWord n I j) (k : Fin (n+j+1)) : ↥(I j) :=
    ⟨u.val k, u.property.2 k⟩
  apply Finite.of_injective f
  intro u v huv
  apply Subtype.ext
  funext k
  exact congrArg Subtype.val (congrFun huv k)

noncomputable def blockSite (k : ℕ) : ℕ × ℕ :=
  siteEquiv.symm (diagonalStart n + k)

theorem blockSite_sum_ge (k : ℕ) : n ≤ (blockSite n k).1 + (blockSite n k).2 := by
  by_contra! h
  have hh := (siteIndex_lt_diagonalStart_iff (blockSite n k) n).mpr h
  rw [blockSite, siteIndex_siteEquiv_symm] at hh
  omega

noncomputable def blockNumber (k : ℕ) : ℕ :=
  (blockSite n k).1 + (blockSite n k).2 - n

noncomputable def blockColumn (k : ℕ) : Fin (n + blockNumber n k + 1) :=
  ⟨(blockSite n k).2, by
    have h := blockSite_sum_ge n k
    unfold blockNumber
    omega⟩

noncomputable def blocksVal (w : BlockProduct n I) (k : ℕ) : ℕ :=
  (w (blockNumber n k)).val (blockColumn n k)

theorem blocksVal_mem (w : BlockProduct n I) (k : ℕ) :
    blocksVal n I w k ∈ I (blockNumber n k) :=
  (w (blockNumber n k)).property.2 _

theorem blockNumber_lt_iff (k m : ℕ) :
    blockNumber n k < m ↔ diagonalStart n + k < diagonalStart (n+m) := by
  rw [← siteIndex_siteEquiv_symm (diagonalStart n+k), siteIndex_lt_diagonalStart_iff]
  have h := blockSite_sum_ge n k
  change blockNumber n k < m ↔ (blockSite n k).1 + (blockSite n k).2 < n+m
  unfold blockNumber
  omega

theorem block_eval_eq (w : BlockProduct n I) {j k : ℕ}
    (h : j = k) {a : Fin (n+j+1)} {b : Fin (n+k+1)} (hab : a.val = b.val) :
    (w j).val a = (w k).val b := by
  subst k
  exact congrArg _ (Fin.ext hab)

theorem block_eval_lt (w : BlockProduct n I) {j k : ℕ}
    (h : j = k) {a : Fin (n+j+1)} {b : Fin (n+k+1)} (hab : a.val < b.val) :
    (w j).val a < (w k).val b := by
  subst k
  exact (w j).property.1 hab

theorem blocksVal_on_shell (w : BlockProduct n I) (j i : ℕ) (hi : i < n+j+1) :
    blocksVal n I w (diagonalStart (n+j) + i - diagonalStart n) = (w j).val ⟨i, hi⟩ := by
  let v : ℕ×ℕ := (n+j-i,i)
  have hv0 : v.1 + v.2 = n+j := by dsimp [v]; omega
  have hstart : diagonalStart n ≤ diagonalStart (n+j) + i :=
    le_trans (diagonalStart_strictMono.monotone (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
  have hv : siteIndex v = diagonalStart (n+j)+i := by unfold siteIndex; rw [hv0]
  let k := diagonalStart (n+j) + i - diagonalStart n
  have hs : blockSite n k = v := by
    apply siteIndex_injective
    rw [blockSite, siteIndex_siteEquiv_symm, hv]
    dsimp [k]
    omega
  have hj : blockNumber n k = j := by unfold blockNumber; rw [hs, hv0]; omega
  change (w (blockNumber n k)).val (blockColumn n k) = (w j).val ⟨i, hi⟩
  exact block_eval_eq n I w hj (congrArg Prod.snd hs)

theorem blocksVal_strictMono
    (hI : ∀ j k, j < k → ∀ a ∈ I j, ∀ b ∈ I k, a < b) (w : BlockProduct n I) :
    StrictMono (blocksVal n I w) := by
  intro k l hkl
  have hsite : siteIndex (blockSite n k) < siteIndex (blockSite n l) := by
    simp only [blockSite, siteIndex_siteEquiv_symm]
    omega
  rcases siteIndex_lt_iff.mp hsite with hs | ⟨hs, hcol⟩
  · have h1 := blockSite_sum_ge n k
    have h2 := blockSite_sum_ge n l
    have hl : blockNumber n k < blockNumber n l := by unfold blockNumber; omega
    exact hI _ _ hl _ (blocksVal_mem _ _ _ _) _ (blocksVal_mem _ _ _ _)
  · have he : blockNumber n k = blockNumber n l := by unfold blockNumber; rw [hs]
    exact block_eval_lt n I w he hcol

noncomputable def blockTail
    (hI : ∀ j k, j < k → ∀ a ∈ I j, ∀ b ∈ I k, a < b) (w : BlockProduct n I) :
    Increasing := ⟨blocksVal n I w, blocksVal_strictMono n I hI w⟩

theorem blockTail_continuous
    (hI : ∀ j k, j < k → ∀ a ∈ I j, ∀ b ∈ I k, a < b) :
    Continuous (blockTail n I hI) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  exact ((continuous_apply (blockColumn n k)).comp continuous_subtype_val).comp (continuous_apply _)

end BlockProduct

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarBlocks

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarFusionStep
section
                                    

set_option autoImplicit false

open Set Topology

namespace HypersmoothCounterexamples

abbrev BitFamily (L : Set ℕ) := RamseyCone L → ℕ → Bool

def EvenTailAgreement {L : Set ℕ} (h : BitFamily L) : Prop :=
  ∀ x y : RamseyCone L, (∃ n, ∀ k ≥ n, x.val.val k = y.val.val k) →
    ∃ n, ∀ k ≥ n, h x k = h y k

/-- A pair of finite prefixes ending at a shell boundary, with a common reservoir. -/
structure PlanarFusionPair (L : Set ℕ) where
  depth : ℕ
  seeds : Bool → RamseyCone L
  overlap : ∀ n < depth, ∀ j < n,
    (seeds false).val.val (diagonalStart n+j+1) = (seeds true).val.val (diagonalStart n+j)
  pool : Set ℕ
  pool_subset : pool ⊆ L
  pool_infinite : pool.Infinite
  pool_above : ∀ b i, i < diagonalStart depth → ∀ j ∈ pool, (seeds b).val.val i < j

def PlanarFusionPair.Extends {L : Set ℕ} (p : PlanarFusionPair L)
    (x : Bool → RamseyCone L) : Prop :=
  (∀ b k, k < diagonalStart p.depth → (x b).val.val k = (p.seeds b).val.val k) ∧
  (∀ b k, diagonalStart p.depth ≤ k → (x b).val.val k ∈ p.pool)

namespace PlanarFusionPair

variable {L : Set ℕ}

set_option maxHeartbeats 1000000 in
theorem exists_fusion_step (p : PlanarFusionPair L) (h : BitFamily L) (hh : Measurable h)
    (hEven : EvenTailAgreement h) (bound : ℕ) :
    ∃ (q : PlanarFusionPair L) (k : ℕ), p.depth < q.depth ∧ bound < k ∧
      p.Extends q.seeds ∧ q.pool ⊆ p.pool ∧
      ∀ x, q.Extends x → p.Extends x ∧ h (x false) k = h (x true) k := by
  classical
  let cut := diagonalStart p.depth
  have pre' (b : Bool) := prependIncreasing_cone cut (p.seeds b) p.pool_subset (p.pool_above b)
  choose pre hpre hpre_eq using pre'
  let A (n : ℕ) : Set (RamseyCone p.pool) :=
    {x | ∀ k ≥ n, h (pre false x) k = h (pre true x) k}
  let B (b : Bool) (k : ℕ) : Set (RamseyCone p.pool) := {x | h (pre b x) k = true}
  have hbit (b : Bool) (k : ℕ) : Measurable (fun x => h (pre b x) k) :=
    (measurable_pi_apply k).comp (hh.comp (hpre b).measurable)
  have hA (n : ℕ) : MeasurableSet (A n) := by
    let E (k : ℕ) : Set (RamseyCone p.pool) :=
      if n ≤ k then {x | h (pre false x) k = h (pre true x) k} else univ
    have hE : A n = ⋂ k : ℕ, E k := by ext x; simp [A, E]
    rw [hE]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : n ≤ k
    · simpa only [E, if_pos hk] using measurableSet_eq_fun (hbit false k) (hbit true k)
    · simp [E, hk]
  have hB (b : Bool) (k : ℕ) : MeasurableSet (B b k) :=
    hbit b k (measurableSet_singleton true)
  let Tests : ℕ ⊕ (Bool × ℕ) → Set (RamseyCone p.pool) :=
    Sum.elim A (fun bk => B bk.1 bk.2)
  obtain ⟨M, hMp, hM, htests⟩ := ramsey_read_relative_sets p.pool p.pool_infinite Tests
    (fun i => Sum.rec hA (fun bk => hB bk.1 bk.2) i)
  let r (j : ℕ) := p.depth + j + 1
  obtain ⟨I, hIM, horder, hex, hcolor⟩ :=
    exists_overlap_alphabets r (fun j => Nat.succ_pos _) M hM
  let f (w : BlockProduct p.depth I) : RamseyCone M :=
    ⟨blockTail p.depth I horder w, by
      rintro _ ⟨i, rfl⟩
      exact hIM _ (blocksVal_mem p.depth I w i)⟩
  have hf : Continuous f := (blockTail_continuous p.depth I horder).subtype_mk _
  let lift (x : RamseyCone M) : RamseyCone p.pool := ⟨x.val, x.prop.trans hMp⟩
  let V (n : ℕ) : Set (RamseyCone M) := {x | lift x ∈ A n}
  have hVo (n : ℕ) : IsOpen (V n) := by
    apply subtype_isOpen_of_prefix
    intro x hx
    obtain ⟨len, he⟩ := htests (.inl n)
    exact ⟨len, fun y hy => (he (lift x) (lift y) x.prop y.prop hy).mp hx⟩
  have hCover : (univ : Set (BlockProduct p.depth I)) ⊆ ⋃ n : ℕ, f ⁻¹' V n := by
    intro w _
    have he : ∃ n, ∀ k ≥ n, (pre false (lift (f w))).val.val k =
        (pre true (lift (f w))).val.val k := by
      refine ⟨cut, fun k hk => ?_⟩
      have hkk : cut + (k-cut) = k := by omega
      rw [← hkk, hpre_eq, hpre_eq, prependIncreasing_tail, prependIncreasing_tail]
    obtain ⟨n, hn⟩ := hEven _ _ he
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover (fun n => f ⁻¹' V n)
    (fun n => (hVo n).preimage hf) hCover
  let k := max bound (J.sup id) + 1
  have hFresh : bound < k := by dsimp [k]; omega
  have hAgree (w : BlockProduct p.depth I) : h (pre false (lift (f w))) k =
      h (pre true (lift (f w))) k := by
    have hw := hJ (show w ∈ (univ : Set (BlockProduct p.depth I)) from mem_univ _)
    rw [mem_iUnion] at hw
    obtain ⟨j, hj⟩ := hw
    rw [mem_iUnion] at hj
    obtain ⟨hjJ, hj⟩ := hj
    have hle : j ≤ J.sup id := Finset.le_sup (f := id) hjJ
    exact hj k (by dsimp [k]; omega)
  choose len hlen using fun b : Bool => htests (.inr (b,k))
  let m := max (len false) (len true)+1
  have hm : 0 < m := Nat.succ_pos _
  have hLen (b : Bool) : len b ≤ m := by cases b <;> simp [m] <;> omega
  have hCut (i : ℕ) (hi : i < m) : cut+i < diagonalStart (p.depth+m) := by
    have hgap (n a : ℕ) : diagonalStart n + a ≤ diagonalStart (n+a) := by
      induction a with
      | zero => simp
      | succ a ih =>
        change diagonalStart n + (a+1) ≤ diagonalStart (n+(a+1))
        rw [show n+(a+1) = (n+a)+1 by omega, diagonalStart_succ]
        omega
    exact (Nat.add_lt_add_left hi _).trans_le (hgap p.depth m)
  let complete (u : ∀ j : Fin m, BlockWord p.depth I j.val) : BlockProduct p.depth I :=
    fun j => if hj : j < m then u ⟨j,hj⟩ else (hex j).some
  have hcomplete (u : ∀ j : Fin m, BlockWord p.depth I j.val) (j : Fin m) :
      complete u j.val = u j := by simp [complete, j.isLt]
  let c (u : ∀ j : Fin m, BlockWord p.depth I j.val) :=
    h (pre false (lift (f (complete u)))) k
  obtain ⟨u, v, hoverlap, hSame⟩ := hcolor m hm c
  let side (b : Bool) : ∀ j : Fin m, BlockWord p.depth I j.val := if b then v else u
  let U (b : Bool) := complete (side b)
  let nextSeed (b : Bool) := pre b (lift (f (U b)))
  have hnextSeed (b : Bool) :
      (nextSeed b).val = prependIncreasing cut (p.seeds b).val (blockTail p.depth I horder (U b))
        (fun i hi j => p.pool_above b i hi _
          (hMp (hIM (blockNumber p.depth j) (blocksVal_mem p.depth I (U b) j)))) :=
    hpre_eq b _
  have hseedPrefix (b : Bool) (i : ℕ) (hi : i < cut) :
      (nextSeed b).val.val i = (p.seeds b).val.val i := by
    rw [hnextSeed, prependIncreasing_prefix _ _ _ _ _ hi]
  have hseedTail (b : Bool) (i : ℕ) :
      (nextSeed b).val.val (cut+i) = blocksVal p.depth I (U b) i := by
    rw [hnextSeed, prependIncreasing_tail]
    rfl
  have hbase (b : Bool) (i : ℕ) (hi : cut ≤ i) : (nextSeed b).val.val i ∈ M := by
    rw [← show cut + (i-cut) = i by omega, hseedTail]
    exact hIM _ (blocksVal_mem _ _ _ _)
  have hblock (b : Bool) (j : Fin m) (i : ℕ) (hi : i < p.depth+j.val+1) :
      (nextSeed b).val.val (diagonalStart (p.depth+j.val)+i) = (side b j).val ⟨i,hi⟩ := by
    have hle : cut ≤ diagonalStart (p.depth+j.val)+i :=
      le_trans (diagonalStart_strictMono.monotone (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
    rw [← show cut+(diagonalStart (p.depth+j.val)+i-cut) = diagonalStart (p.depth+j.val)+i by omega,
      hseedTail, blocksVal_on_shell]
    exact congrArg (fun z : BlockWord p.depth I j.val => z.val ⟨i,hi⟩) (hcomplete (side b) j)
  have hIne : (I (m-1)).Nonempty := by
    obtain ⟨z⟩ := hex (m-1)
    exact ⟨z.val ⟨0,Nat.succ_pos _⟩, z.property.2 _⟩
  let top := (I (m-1)).max' hIne
  have htop (j a : ℕ) (hj : j < m) (ha : a ∈ I j) : a ≤ top := by
    by_cases he : j = m-1
    · subst j
      exact Finset.le_max' _ _ ha
    · exact (horder j (m-1) (by omega) a ha _ (Finset.max'_mem _ hIne)).le
  let q : PlanarFusionPair L :=
    { depth := p.depth + m
      seeds := nextSeed
      overlap := by
        intro n hn j hj
        by_cases hold : n < p.depth
        · have hidx : diagonalStart n+j+1 < cut := by
            have hb := diagonalStart_strictMono.monotone (show n+1 ≤ p.depth by omega)
            rw [diagonalStart_succ] at hb
            omega
          rw [hseedPrefix false _ hidx, hseedPrefix true _ (by omega)]
          exact p.overlap n hold j hj
        · let t : Fin m := ⟨n-p.depth, by omega⟩
          have ht : p.depth+t.val = n := by dsimp [t]; omega
          have hi₁ : j+1 < p.depth+t.val+1 := by omega
          have hi₂ : j < p.depth+t.val+1 := by omega
          have h₁ := hblock false t (j+1) hi₁
          have h₂ := hblock true t j hi₂
          have he₁ : diagonalStart (p.depth+t.val)+(j+1) = diagonalStart n+j+1 := by
            rw [ht]; omega
          have he₂ : diagonalStart (p.depth+t.val)+j = diagonalStart n+j := by rw [ht]
          rw [← he₁, ← he₂, h₁, h₂]
          exact (hoverlap t).1 ⟨j,hi₂⟩ ⟨j+1,hi₁⟩ rfl
      pool := M ∩ Ioi top
      pool_subset := inter_subset_left.trans (hMp.trans p.pool_subset)
      pool_infinite := tail_infinite hM top
      pool_above := by
        intro b i hi a ha
        by_cases hprei : i < cut
        · rw [hseedPrefix b i hprei]
          exact p.pool_above b i hprei a (hMp ha.1)
        · have he : cut+(i-cut)=i := by omega
          have hj : blockNumber p.depth (i-cut) < m :=
            (blockNumber_lt_iff p.depth (i-cut) m).mpr (by
              change cut+(i-cut) < diagonalStart (p.depth+m)
              rw [he]
              exact hi)
          rw [← he, hseedTail]
          exact (htop _ _ hj (blocksVal_mem _ _ _ _)).trans_lt ha.2 }
  have hdepth : p.depth < q.depth := by dsimp [q]; omega
  have hCutMono : cut ≤ diagonalStart q.depth := diagonalStart_strictMono.monotone hdepth.le
  have hpq : p.Extends q.seeds := ⟨hseedPrefix, fun b i hi => hMp (hbase b i hi)⟩
  have hsubset : q.pool ⊆ p.pool := inter_subset_left.trans hMp
  refine ⟨q,k,hdepth,hFresh,hpq,hsubset, fun x hx => ⟨?_,?_⟩⟩
  · refine ⟨fun b i hi => (hx.1 b i (hi.trans_le hCutMono)).trans (hseedPrefix b i hi), ?_⟩
    intro b i hi
    by_cases hqi : i < diagonalStart q.depth
    · rw [hx.1 b i hqi]
      exact hMp (hbase b i hi)
    · exact hsubset (hx.2 b i (Nat.le_of_not_lt hqi))
  · have recover (b : Bool) : h (x b) k = h (nextSeed b) k := by
      have hDrop (i : ℕ) : (dropIncreasing cut (x b).val).val i ∈ M := by
        change (x b).val.val (cut+i) ∈ M
        by_cases hi : cut+i < diagonalStart q.depth
        · rw [hx.1 b _ hi]
          exact hbase b _ (Nat.le_add_right _ _)
        · exact (hx.2 b _ (Nat.le_of_not_lt hi)).1
      let y : RamseyCone M := ⟨dropIncreasing cut (x b).val, by
        rintro _ ⟨i,rfl⟩; exact hDrop i⟩
      have hyPrefix : ∀ i < len b, (lift y).val.val i = (lift (f (U b))).val.val i := by
        intro i hi
        have hxpre := hx.1 b (cut+i) (hCut i (hi.trans_le (hLen b)))
        rw [hseedTail] at hxpre
        exact hxpre
      have he : pre b (lift y) = x b := by
        apply Subtype.ext
        rw [hpre_eq]
        exact prepend_drop_of_prefix cut _ _
          (fun i hi => ((hx.1 b i (hi.trans_le hCutMono)).trans (hseedPrefix b i hi)).symm)
      have htest := hlen b (lift (f (U b))) (lift y) (f (U b)).prop y.prop hyPrefix
      change (h (nextSeed b) k = true) ↔ (h (pre b (lift y)) k = true) at htest
      rw [he] at htest
      cases h₁ : h (x b) k <;> cases h₂ : h (nextSeed b) k <;> simp [h₁,h₂] at htest ⊢
    rw [recover false, recover true]
    exact hSame.trans (hAgree (complete v))

end PlanarFusionPair

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarFusionStep

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarFusion
section
                                        

set_option autoImplicit false

open Set

namespace HypersmoothCounterexamples

/-- The chosen shell words have both global overlap and arbitrarily late agreeing bits. -/
theorem planar_fusion {L : Set ℕ} (hL : L.Infinite) (h : BitFamily L)
    (hh : Measurable h) (hEven : EvenTailAgreement h) :
    ∃ x y : RamseyCone L,
      (∀ n j, j < n → x.val.val (diagonalStart n+j+1) = y.val.val (diagonalStart n+j)) ∧
      ∀ a, ∃ k ≥ a, h x k = h y k := by
  classical
  let z : RamseyCone L := ⟨enumerateIncreasing L hL, by simp [RamseyCone]⟩
  let first : PlanarFusionPair L :=
    { depth := 0
      seeds := fun _ => z
      overlap := by simp
      pool := L
      pool_subset := subset_rfl
      pool_infinite := hL
      pool_above := by simp [diagonalStart] }
  have step (s : PlanarFusionPair L × ℕ) :=
    s.1.exists_fusion_step h hh hEven s.2
  let next (s : PlanarFusionPair L × ℕ) : PlanarFusionPair L × ℕ :=
    ⟨(step s).choose, (step s).choose_spec.choose⟩
  let S (n : ℕ) := next^[n] (first, 0)
  let P (n : ℕ) := (S n).1
  let k (n : ℕ) := (S n).2
  have hnext (n : ℕ) : S (n+1) = next (S n) := Function.iterate_succ_apply' _ _ _
  have hstep (n : ℕ) :
      (P n).depth < (P (n+1)).depth ∧ k n < k (n+1) ∧
      (P n).Extends (P (n+1)).seeds ∧ (P (n+1)).pool ⊆ (P n).pool ∧
      ∀ x, (P (n+1)).Extends x →
        (P n).Extends x ∧ h (x false) (k (n+1)) = h (x true) (k (n+1)) := by
    dsimp only [P, k]
    rw [hnext]
    exact (step (S n)).choose_spec.choose_spec
  have hDepth := strictMono_nat_of_lt_succ (fun n => (hstep n).1)
  have hKmono := strictMono_nat_of_lt_succ (fun n => (hstep n).2.1)
  have hDepthGe (n : ℕ) : n ≤ (P n).depth :=
    increasing_index_le ⟨fun j => (P j).depth, hDepth⟩ n
  have hKge (n : ℕ) : n ≤ k n := increasing_index_le ⟨k, hKmono⟩ n
  have hCut (i : ℕ) : i < diagonalStart (P (i+1)).depth :=
    (Nat.lt_succ_self i).trans_le ((hDepthGe (i+1)).trans (diagonalStart_ge _))
  have hSeed (n m : ℕ) (hnm : n ≤ m) (b : Bool) (i : ℕ)
      (hi : i < diagonalStart (P n).depth) :
      ((P m).seeds b).val.val i = ((P n).seeds b).val.val i := by
    refine Nat.le_induction rfl (fun j hj hprev => ?_) m hnm
    have hjcut := diagonalStart_strictMono.monotone (hDepth.monotone hj)
    exact (((hstep j).2.2.1).1 b i (hi.trans_le hjcut)).trans hprev
  let u (b : Bool) (i : ℕ) := ((P (i+1)).seeds b).val.val i
  have hSeedEq (n : ℕ) (b : Bool) (i : ℕ) (hi : i < diagonalStart (P n).depth) :
      u b i = ((P n).seeds b).val.val i := by
    let m := max (i+1) n
    exact (hSeed (i+1) m (le_max_left _ _) b i (hCut i)).symm.trans
      (hSeed n m (le_max_right _ _) b i hi)
  have hu (b : Bool) : StrictMono (u b) := by
    intro i j hij
    rw [hSeedEq _ _ i (hij.trans (hCut j)), hSeedEq _ _ j (hCut j)]
    exact ((P (j+1)).seeds b).val.property hij
  let x (b : Bool) : RamseyCone L := ⟨⟨u b,hu b⟩, by
    rintro _ ⟨i,rfl⟩
    exact ((P (i+1)).seeds b).prop (mem_range_self i)⟩
  have hRestricts (n m : ℕ) (hnm : n ≤ m) (y : Bool → RamseyCone L) :
      (P m).Extends y → (P n).Extends y := by
    refine Nat.le_induction id (fun j hj hprev hcur => ?_) m hnm
    exact hprev ((hstep j).2.2.2.2 y hcur).1
  have hX (n : ℕ) : (P n).Extends x := by
    refine ⟨hSeedEq n, ?_⟩
    intro b i hi
    let m := max n (i+1)
    have him : i < diagonalStart (P (m+1)).depth :=
      (hCut i).trans_le (diagonalStart_strictMono.monotone
        (hDepth.monotone ((le_max_right _ _).trans (Nat.le_succ m))))
    change u b i ∈ (P n).pool
    rw [hSeedEq _ _ _ him]
    exact (hRestricts n m (le_max_left _ _) _ ((hstep m).2.2.1)).2 b i hi
  refine ⟨x false,x true, ?_, ?_⟩
  · intro n j hj
    have hn : n < (P (n+1)).depth := (Nat.lt_succ_self n).trans_le (hDepthGe _)
    have hidx : diagonalStart n + j + 1 < diagonalStart (P (n+1)).depth := by
      have hh := diagonalStart_strictMono.monotone (Nat.succ_le_of_lt hn)
      rw [diagonalStart_succ] at hh
      omega
    change u false _ = u true _
    rw [hSeedEq (n+1) false _ hidx, hSeedEq (n+1) true _ (by omega)]
    exact (P (n+1)).overlap n hn j hj
  · intro a
    exact ⟨k (a+1), (Nat.le_succ a).trans (hKge (a+1)),
      ((hstep a).2.2.2.2 x (hX (a+1))).2⟩

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarFusion

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarProper
section
                                      
                                                      
                                     

set_option autoImplicit false

open Set Topology

namespace HypersmoothCounterexamples

theorem isClosed_increasing : IsClosed {s : ℕ → ℕ | StrictMono s} := by
  have heq : {s : ℕ → ℕ | StrictMono s} = ⋂ n : ℕ, {s | s n < s (n+1)} := by
    ext s
    simp only [mem_setOf_eq, mem_iInter]
    exact ⟨fun h n => h (Nat.lt_succ_self n), strictMono_nat_of_lt_succ⟩
  rw [heq]
  apply isClosed_iInter
  intro n
  let f : (ℕ → ℕ) → ℕ × ℕ := fun s => (s n,s (n+1))
  have hf : Continuous f := (continuous_apply n).prodMk (continuous_apply (n+1))
  change IsClosed (f ⁻¹' {p : ℕ × ℕ | p.1 < p.2})
  exact (isClosed_discrete _).preimage hf

theorem continuous_increasingShift (a : ℕ × ℕ) : Continuous (increasingShift a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_apply (siteIndex (siteEquiv.symm n + a))).comp continuous_subtype_val

theorem isProperMap_increasingShift (a : ℕ × ℕ) : IsProperMap (increasingShift a) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_increasingShift a, ?_⟩
  intro K hK
  have hb (n : ℕ) : BddAbove ((fun x : Increasing => x.val (siteIndex (n,0))) '' K) :=
    hK.bddAbove_image ((continuous_apply (siteIndex (n,0))).comp continuous_subtype_val).continuousOn
  choose M hM using hb
  let B : Set (ℕ → ℕ) := {s | ∀ n, s n ≤ M n}
  have hB : IsCompact B :=
    isCompact_pi_infinite (s := fun n => Iic (M n)) fun n => (Set.finite_Iic (M n)).isCompact
  have hsub : IsProperMap (Subtype.val : Increasing → ℕ → ℕ) :=
    (IsClosedEmbedding.subtypeVal isClosed_increasing).isProperMap
  apply (hsub.isCompact_preimage hB).of_isClosed_subset
    (hK.isClosed.preimage (continuous_increasingShift a))
  intro x hx n
  have hbound : (increasingShift a x).val (siteIndex (n,0)) ≤ M n :=
    hM n (mem_image_of_mem _ hx)
  change planarLabel (increasingShift a x) (n,0) ≤ M n at hbound
  rw [planarLabel_increasingShift] at hbound
  apply le_trans (x.property.monotone ?_) hbound
  change n ≤ diagonalStart ((n + a.1)+(0 + a.2)) + (0+a.2)
  have hbnd := diagonalStart_ge ((n + a.1)+(0 + a.2))
  omega

theorem isClosed_shiftChart_projection {C : Set Increasing} (hC : IsClosed C)
    (a b : ℕ × ℕ) {P : Set (C × C)} (hP : IsClosed P) :
    IsClosed {x : C | ∃ y : C, (x,y) ∈ P ∧ increasingShift a x.val = increasingShift b y.val} := by
  let f : C × C → C × Increasing := Prod.map id (increasingShift b ∘ Subtype.val)
  let g : C → C × Increasing := fun x => (x, increasingShift a x.val)
  have hf : IsProperMap f := isProperMap_id.prodMap
    ((isProperMap_increasingShift b).comp (IsClosedEmbedding.subtypeVal hC).isProperMap)
  have hg : Continuous g := continuous_id.prodMk ((continuous_increasingShift a).comp continuous_subtype_val)
  have heq : {x : C | ∃ y : C, (x,y) ∈ P ∧ increasingShift a x.val = increasingShift b y.val} =
      g ⁻¹' (f '' P) := by
    ext x
    constructor
    · rintro ⟨y, hy, hEq⟩
      exact ⟨(x,y), hy, Prod.ext rfl hEq.symm⟩
    · rintro ⟨⟨w,y⟩, hw, he⟩
      have hwx : w = x := congrArg Prod.fst he
      subst w
      exact ⟨y, hw, (congrArg Prod.snd he).symm⟩
  rw [heq]
  exact (hf.isClosedMap P hP).preimage hg

theorem increasingShift_eq_iff (a b : ℕ × ℕ) (s t : Increasing) :
    increasingShift a s = increasingShift b t ↔
      ∀ v, planarLabel s (v+a) = planarLabel t (v+b) := by
  constructor
  · intro h v
    simpa only [planarLabel_increasingShift] using congrArg (fun r => planarLabel r v) h
  · intro h
    apply planarLabel_injective
    funext v
    simpa only [planarLabel_increasingShift] using h v

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarProper

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarSelector
section
                                    
                                   
                            

set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace HypersmoothCounterexamples

variable {C : Set Increasing}

/-- A prefix is viable when it extends to a member of the same classifier fiber. -/
def PrefixViable (q : C → ℕ → Bool) {n : ℕ} (p : Fin n → ℕ) (x : C) : Prop :=
  ∃ y : C, q y = q x ∧ ∀ i : Fin n, y.val.val i = p i

theorem measurableSet_prefixViable (hC : IsClosed C) {q : C → ℕ → Bool} (hq : Continuous q)
    (hsub : ∀ x y, q x = q y → IncreasingRelation x.val y.val) {n : ℕ} (p : Fin n → ℕ) :
    MeasurableSet {x : C | PrefixViable q p x} := by
  let P : Set (C × C) := {z | q z.2 = q z.1 ∧ ∀ i : Fin n, z.2.val.val i = p i}
  have hP : IsClosed P := by
    let hp (i : Fin n) : (C × C) → ℕ := fun z => z.2.val.val i
    have hc (i : Fin n) : Continuous (hp i) := (continuous_apply (i : ℕ)).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    have heq : P = {z : C × C | q z.2 = q z.1} ∩ ⋂ i : Fin n, {z | hp i z = p i} := by
      ext z
      simp [P,hp]
    rw [heq]
    exact (isClosed_eq (hq.comp continuous_snd) (hq.comp continuous_fst)).inter
      (isClosed_iInter fun i => isClosed_eq (hc i) continuous_const)
  let D (a b : ℕ×ℕ) : Set C :=
    {x | ∃ y : C, (x,y) ∈ P ∧ increasingShift a x.val = increasingShift b y.val}
  have hD (a b : ℕ×ℕ) : IsClosed (D a b) := isClosed_shiftChart_projection hC a b hP
  have heq : {x : C | PrefixViable q p x} = ⋃ a : ℕ×ℕ, ⋃ b : ℕ×ℕ, D a b := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨y,hy,hpref⟩
      obtain ⟨a,b,hab⟩ := hsub x y hy.symm
      exact ⟨a,b,y,⟨hy,hpref⟩,(increasingShift_eq_iff a b x.val y.val).mpr hab⟩
    · rintro ⟨a,b,y,⟨hy,hpref⟩,_⟩
      exact ⟨y,hy,hpref⟩
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => (hD a b).measurableSet

theorem prefixViable_extend {q : C → ℕ → Bool} {x : C} {n : ℕ} {p : Fin n → ℕ}
    (hp : PrefixViable q p x) : ∃ d : ℕ, PrefixViable q (Fin.snoc p d) x := by
  obtain ⟨y,hy,hpref⟩ := hp
  refine ⟨y.val.val n,y,hy,fun i => ?_⟩
  refine Fin.lastCases (motive := fun i =>
    y.val.val ↑i = (Fin.snoc p (y.val.val n) : Fin (n+1) → ℕ) i) ?_ ?_ i
  · simp
  · intro j
    simpa using hpref j

def viableNext {q : C → ℕ → Bool} {x : C} {n : ℕ} {p : Fin n → ℕ}
    (hp : PrefixViable q p x) : ℕ := by
  classical
  exact Nat.find (prefixViable_extend hp)

/-- Beginning with the empty viable prefix, keep the least viable next digit. -/
def canonicalPrefixes (q : C → ℕ → Bool) (x : C) :
    (n : ℕ) → {p : Fin n → ℕ // PrefixViable q p x}
  | 0 => ⟨fun _ => 0, x, rfl, fun i => Fin.elim0 i⟩
  | n+1 => by
    classical
    let p := canonicalPrefixes q x n
    refine ⟨Fin.snoc p.val (viableNext p.property), ?_⟩
    exact Nat.find_spec (prefixViable_extend p.property)

theorem canonicalPrefixes_succ (q : C → ℕ → Bool) (x : C) (n : ℕ) :
    (canonicalPrefixes q x (n+1)).val =
      Fin.snoc (canonicalPrefixes q x n).val
        (viableNext (canonicalPrefixes q x n).property) := by
  rfl

@[simp] theorem canonicalPrefixes_castSucc (q : C → ℕ → Bool) (x : C) (n : ℕ) (i : Fin n) :
    (canonicalPrefixes q x (n+1)).val i.castSucc = (canonicalPrefixes q x n).val i := by
  rw [canonicalPrefixes_succ, Fin.snoc_castSucc]

def canonicalSeq (q : C → ℕ → Bool) (x : C) (n : ℕ) : ℕ :=
  (canonicalPrefixes q x (n+1)).val (Fin.last n)

theorem canonicalPrefixes_eval (q : C → ℕ → Bool) (x : C) (n : ℕ) (i : Fin n) :
    (canonicalPrefixes q x n).val i = canonicalSeq q x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases (motive := fun i =>
      (canonicalPrefixes q x (n+1)).val i = canonicalSeq q x i) ?_ ?_ i
    · rfl
    · intro j
      rw [canonicalPrefixes_castSucc]
      exact ih j

theorem canonicalSeq_strictMono (q : C → ℕ → Bool) (x : C) : StrictMono (canonicalSeq q x) := by
  intro i j hij
  obtain ⟨y,_,hy⟩ := (canonicalPrefixes q x (j+1)).property
  have hi : y.val.val i = canonicalSeq q x i := (hy (⟨i, by omega⟩ : Fin (j+1))).trans
    (canonicalPrefixes_eval q x (j+1) ⟨i,by omega⟩)
  have hj : y.val.val j = canonicalSeq q x j :=
    (hy (Fin.last j)).trans (canonicalPrefixes_eval q x (j+1) (Fin.last j))
  rw [← hi,← hj]
  exact y.val.property hij

def canonicalEnumeration (q : C → ℕ → Bool) (x : C) : Increasing :=
  ⟨canonicalSeq q x, canonicalSeq_strictMono q x⟩

def prefixWitness (q : C → ℕ → Bool) (x : C) (n : ℕ) : C :=
  (canonicalPrefixes q x n).property.choose

theorem prefixWitness_q (q : C → ℕ → Bool) (x : C) (n : ℕ) :
    q (prefixWitness q x n) = q x := (canonicalPrefixes q x n).property.choose_spec.1

theorem prefixWitness_eval (q : C → ℕ → Bool) (x : C) (n : ℕ) (i : Fin n) :
    (prefixWitness q x n).val.val i = canonicalSeq q x i :=
  ((canonicalPrefixes q x n).property.choose_spec.2 i).trans (canonicalPrefixes_eval q x n i)

theorem tendsto_prefixWitness (q : C → ℕ → Bool) (x : C) :
    Tendsto (fun n => (prefixWitness q x n).val) atTop (𝓝 (canonicalEnumeration q x)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with n hn
  exact (prefixWitness_eval q x n ⟨i,hn⟩).symm

theorem canonicalEnumeration_mem (hC : IsClosed C) (q : C → ℕ → Bool) (x : C) :
    canonicalEnumeration q x ∈ C :=
  hC.mem_of_tendsto (tendsto_prefixWitness q x) (Eventually.of_forall fun n => (prefixWitness q x n).property)

def canonicalSelector (hC : IsClosed C) (q : C → ℕ → Bool) (x : C) : C :=
  ⟨canonicalEnumeration q x, canonicalEnumeration_mem hC q x⟩

theorem canonicalSelector_q (hC : IsClosed C) {q : C → ℕ → Bool} (hq : Continuous q) (x : C) :
    q (canonicalSelector hC q x) = q x := by
  have hlim : Tendsto (prefixWitness q x) atTop (𝓝 (canonicalSelector hC q x)) :=
    tendsto_subtype_rng.mpr (tendsto_prefixWitness q x)
  exact (isClosed_eq hq continuous_const).mem_of_tendsto hlim
    (Eventually.of_forall fun n => prefixWitness_q q x n)

theorem canonicalPrefixes_eq (q : C → ℕ → Bool) {x y : C} (hxy : q x = q y) (n : ℕ) :
    (canonicalPrefixes q x n).val = (canonicalPrefixes q y n).val := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [canonicalPrefixes_succ, canonicalPrefixes_succ]
    have hfind : viableNext (canonicalPrefixes q x n).property =
        viableNext (canonicalPrefixes q y n).property := by
      unfold viableNext
      apply Nat.find_congr'
      intro m
      simp only [PrefixViable, hxy, ih]
    rw [hfind, ih]

theorem canonicalSelector_eq (hC : IsClosed C) (q : C → ℕ → Bool) {x y : C} (hxy : q x = q y) :
    canonicalSelector hC q x = canonicalSelector hC q y := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  exact congrFun (canonicalPrefixes_eq q hxy (n+1)) (Fin.last n)

theorem measurableSet_prefixViable_snoc (hC : IsClosed C) {q : C → ℕ → Bool} (hq : Continuous q)
    (hsub : ∀ x y, q x = q y → IncreasingRelation x.val y.val)
    {n : ℕ} {P : C → (Fin n → ℕ)} (hP : Measurable P) (d : ℕ) :
    MeasurableSet {x : C | PrefixViable q (Fin.snoc (P x) d) x} := by
  have heq : {x : C | PrefixViable q (Fin.snoc (P x) d) x} =
      ⋃ p : Fin n → ℕ, {x : C | P x = p} ∩ {x : C | PrefixViable q (Fin.snoc p d) x} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨P x,rfl,h⟩, by rintro ⟨p,hp,h⟩; simpa only [hp] using h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun p => (hP (measurableSet_singleton p)).inter
    (measurableSet_prefixViable hC hq hsub (Fin.snoc p d))

theorem measurable_canonicalPrefixes (hC : IsClosed C) {q : C → ℕ → Bool} (hq : Continuous q)
    (hsub : ∀ x y, q x = q y → IncreasingRelation x.val y.val) (n : ℕ) :
    Measurable (fun x : C => (canonicalPrefixes q x n).val) := by
  classical
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let g (x : C) := viableNext (canonicalPrefixes q x n).property
    have hg : Measurable g := by
      apply measurable_to_countable'
      intro d
      have heq : g ⁻¹' {d} =
          {x : C | PrefixViable q (Fin.snoc (canonicalPrefixes q x n).val d) x} ∩
          ⋂ k : ℕ, ⋂ _ : k < d,
            {x : C | PrefixViable q (Fin.snoc (canonicalPrefixes q x n).val k) x}ᶜ := by
        ext x
        simp only [g,viableNext,mem_preimage,mem_singleton_iff,Nat.find_eq_iff,mem_inter_iff,
          mem_iInter,mem_compl_iff,mem_setOf_eq]
      rw [heq]
      exact (measurableSet_prefixViable_snoc hC hq hsub ih d).inter
        (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ : k < d =>
          (measurableSet_prefixViable_snoc hC hq hsub ih k).compl)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases (motive := fun i => Measurable
      (fun x : C => (canonicalPrefixes q x (n+1)).val i)) ?_ ?_ i
    · simpa only [canonicalPrefixes_succ, Fin.snoc_last] using hg
    · intro j
      simpa only [canonicalPrefixes_castSucc] using (measurable_pi_apply j).comp ih

theorem measurable_canonicalSelector (hC : IsClosed C) {q : C → ℕ → Bool} (hq : Continuous q)
    (hsub : ∀ x y, q x = q y → IncreasingRelation x.val y.val) :
    Measurable (canonicalSelector hC q) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.last i)).comp (measurable_canonicalPrefixes hC hq hsub (i+1))

end HypersmoothCounterexamples

end
end
-- END COMPLETE MODULE HypersmoothProof.PlanarSelector

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarParity
section
                                      

set_option autoImplicit false
noncomputable section

open Set

namespace HypersmoothCounterexamples

theorem planar_witness_balance {s t : Increasing} {a b a' b' : ℕ × ℕ}
    (h : ∀ v, planarLabel s (v+a) = planarLabel t (v+b))
    (h' : ∀ v, planarLabel s (v+a') = planarLabel t (v+b')) :
    a+b' = a'+b := by
  apply planarLabel_free s
  funext v
  change planarLabel s (v+(a+b')) = planarLabel s (v+(a'+b))
  calc
    planarLabel s (v+(a+b')) = planarLabel s ((v+b')+a) := by rw [add_comm a b', add_assoc]
    _ = planarLabel t ((v+b')+b) := h (v+b')
    _ = planarLabel t ((v+b)+b') := by rw [add_right_comm]
    _ = planarLabel s ((v+b)+a') := (h' (v+b)).symm
    _ = planarLabel s (v+(a'+b)) := by rw [add_assoc,add_comm b a']

theorem planar_witness_compose {s t u : Increasing} {a b c d : ℕ × ℕ}
    (h : ∀ v, planarLabel s (v+a) = planarLabel t (v+b))
    (h' : ∀ v, planarLabel t (v+c) = planarLabel u (v+d)) :
    ∀ v, planarLabel s (v+(c+a)) = planarLabel u (v+(b+d)) := by
  intro v
  rw [← add_assoc,← add_assoc]
  refine (h (v+c)).trans ?_
  rw [add_right_comm v c b]
  exact h' (v+b)

/-- Odd parity of the second coordinate of the shift displacement. -/
def displacementBit (s t : Increasing) : Bool := by
  classical
  exact decide (∃ a b : ℕ × ℕ, a.2 % 2 ≠ b.2 % 2 ∧
    ∀ v, planarLabel s (v+a) = planarLabel t (v+b))

theorem displacementBit_true_iff (s t : Increasing) :
    displacementBit s t = true ↔ ∃ a b : ℕ × ℕ, a.2 % 2 ≠ b.2 % 2 ∧
      ∀ v, planarLabel s (v+a) = planarLabel t (v+b) := by
  classical
  simp [displacementBit]

theorem displacementBit_eq_of_witness {s t : Increasing} {a b : ℕ × ℕ}
    (h : ∀ v, planarLabel s (v+a) = planarLabel t (v+b)) :
    displacementBit s t = decide (a.2 % 2 ≠ b.2 % 2) := by
  rw [Bool.eq_iff_iff,displacementBit_true_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨a',b',hodd,hagree⟩
    have hs : a.2 + b'.2 = a'.2 + b.2 := congrArg Prod.snd (planar_witness_balance h hagree)
    omega
  · exact fun hodd => ⟨a,b,hodd,h⟩

theorem measurable_displacementBit : Measurable (fun p : Increasing×Increasing => displacementBit p.1 p.2) := by
  let O (a b : ℕ×ℕ) : Set (Increasing×Increasing) := {p |
    a.2 % 2 ≠ b.2 % 2 ∧ increasingShift a p.1 = increasingShift b p.2}
  have hO (a b : ℕ×ℕ) : MeasurableSet (O a b) := by
    by_cases h : a.2 % 2 ≠ b.2 % 2
    · have heq : O a b = ⋂ n : ℕ, {p : Increasing×Increasing |
          (increasingShift a p.1).val n = (increasingShift b p.2).val n} := by
        ext p
        simp only [O,mem_setOf_eq,mem_iInter]
        exact ⟨fun he n => congrArg (fun x : Increasing => x.val n) he.2,
          fun he => ⟨h,Subtype.ext (funext he)⟩⟩
      rw [heq]
      apply MeasurableSet.iInter
      intro n
      have hf : Measurable (fun p : Increasing×Increasing => increasingShift a p.1) :=
        (continuous_increasingShift a).measurable.comp measurable_fst
      have hg : Measurable (fun p : Increasing×Increasing => increasingShift b p.2) :=
        (continuous_increasingShift b).measurable.comp measurable_snd
      exact measurableSet_eq_fun ((measurable_pi_apply n).comp (measurable_subtype_coe.comp hf))
        ((measurable_pi_apply n).comp (measurable_subtype_coe.comp hg))
    · simp [O,h]
  have heq : {p : Increasing×Increasing | displacementBit p.1 p.2 = true} =
      ⋃ a : ℕ×ℕ, ⋃ b : ℕ×ℕ, O a b := by
    ext p
    simp only [O,mem_setOf_eq,mem_iUnion,increasingShift_eq_iff,displacementBit_true_iff]
  have hm : MeasurableSet {p : Increasing×Increasing | displacementBit p.1 p.2 = true} := by
    rw [heq]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => hO a b
  apply measurable_to_countable'
  intro bit
  cases bit with
  | false =>
    have hfalse : (fun p : Increasing×Increasing => displacementBit p.1 p.2) ⁻¹' {false} =
        {p : Increasing×Increasing | displacementBit p.1 p.2 = true}ᶜ := by
      ext p
      change displacementBit p.1 p.2 = false ↔ ¬ displacementBit p.1 p.2 = true
      cases displacementBit p.1 p.2 <;> decide
    rw [hfalse]
    exact hm.compl
  | true => exact hm

theorem displacementBits_equivalence {s t z : Increasing} {a b : ℕ×ℕ}
    (hst : ∀ v, planarLabel s (v+a) = planarLabel t (v+b)) (htz : IncreasingRelation t z) :
    displacementBit s z = displacementBit t z ↔ a.2 % 2 = b.2 % 2 := by
  obtain ⟨c,d,htz⟩ := htz
  rw [displacementBit_eq_of_witness (planar_witness_compose hst htz),
    displacementBit_eq_of_witness htz, decide_eq_decide]
  change (((c.2+a.2)%2 ≠ (b.2+d.2)%2) ↔ (c.2%2 ≠ d.2%2)) ↔ _
  omega

/-- On a closed subspace where the smooth level classifiers are continuous,
the displacement parity eventually equals the difference between Borel bits. -/
theorem exists_eventual_displacement_bits {C : Set Increasing} (hC : IsClosed C)
    (q : ℕ → C → ℕ → Bool) (hqc : ∀ n, Continuous (q n))
    (hsub : ∀ n x y, q n x = q n y → IncreasingRelation x.val y.val)
    (hexh : ∀ x y, IncreasingRelation x.val y.val → ∃ N, ∀ k ≥ N, q k x = q k y) :
    ∃ h : C → ℕ → Bool, Measurable h ∧ ∀ x y (a b : ℕ×ℕ),
      (∀ v, planarLabel x.val (v+a) = planarLabel y.val (v+b)) →
        ∃ N, ∀ k ≥ N, (h x k = h y k ↔ a.2 % 2 = b.2 % 2) := by
  let h (x : C) (n : ℕ) := displacementBit x.val (canonicalSelector hC (q n) x).val
  refine ⟨h, measurable_pi_lambda _ (fun n => ?_), ?_⟩
  · exact measurable_displacementBit.comp (measurable_subtype_coe.prodMk
      (measurable_subtype_coe.comp (measurable_canonicalSelector hC (hqc n) (hsub n))))
  · intro x y a b hab
    obtain ⟨N,hN⟩ := hexh x y ⟨a,b,hab⟩
    refine ⟨N,fun k hk => ?_⟩
    have he := canonicalSelector_eq hC (q k) (hN k hk)
    have hr : IncreasingRelation y.val (canonicalSelector hC (q k) y).val :=
      hsub k y _ (canonicalSelector_q hC (hqc k) y).symm
    change displacementBit x.val (canonicalSelector hC (q k) x).val =
      displacementBit y.val (canonicalSelector hC (q k) y).val ↔ _
    rw [he]
    exact displacementBits_equivalence hab hr

end HypersmoothCounterexamples

end
end
-- END COMPLETE MODULE HypersmoothProof.PlanarParity

-- BEGIN COMPLETE MODULE HypersmoothProof.PlanarObstruction
section
                                   
                                    
                                    

set_option autoImplicit false

open Set

namespace HypersmoothCounterexamples

/-- The common-future relation on increasing antidiagonal arrays is not hypersmooth. -/
theorem not_hypersmooth_increasingRelation : ¬ Hypersmooth IncreasingRelation := by
  classical
  rintro ⟨F, hF, hmono, hunion⟩
  choose q hq hclass using hF
  obtain ⟨M, _, hM, hqc⟩ :=
    exists_continuousOn_ramseyCone q hq univ infinite_univ
  have hsub (n : ℕ) (x y : RamseyCone M) (h : q n x.val = q n y.val) :
      IncreasingRelation x.val y.val := (hunion x.val y.val).mpr
    ⟨n, (hclass n x.val y.val).mpr h⟩
  have hExhaust (x y : RamseyCone M) (h : IncreasingRelation x.val y.val) :
      ∃ N, ∀ k ≥ N, q k x.val = q k y.val := by
    obtain ⟨N,hN⟩ := (hunion x.val y.val).mp h
    refine ⟨N, fun k hk => (hclass k x.val y.val).mp ?_⟩
    have hinc : Monotone (fun n => F n x.val y.val) :=
      monotone_nat_of_le_succ (fun n => hmono n x.val y.val)
    exact hinc hk hN
  obtain ⟨h, hh, hparity⟩ := exists_eventual_displacement_bits
    (isClosed_ramseyCone M) (fun n x => q n x.val) hqc hsub hExhaust
  have hEven : EvenTailAgreement h := by
    intro x y hh
    obtain ⟨n,hn⟩ := hh
    obtain ⟨N,hN⟩ := hparity x y (n,0) (n,0) (increasing_equal_translation_of_tail hn)
    exact ⟨N, fun k hk => (hN k hk).mpr rfl⟩
  obtain ⟨x,y,hOverlap,hAgree⟩ := planar_fusion hM h hh hEven
  obtain ⟨N,hN⟩ := hparity x y (0,1) (1,0) (increasing_overlap_translation hOverlap)
  obtain ⟨k,hk,heq⟩ := hAgree N
  have hcontr := (hN k hk).mp heq
  simp at hcontr

end HypersmoothCounterexamples

end
-- END COMPLETE MODULE HypersmoothProof.PlanarObstruction

-- BEGIN COMPLETE MODULE Solutions.TheoremB
section
                                      
                                         

set_option autoImplicit false

open HypersmoothCounterexamples

theorem HypersmoothCounterexamples.theoremB :
    ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ Hypersmooth (BinaryFreeRelation ℓ) :=
  binary_counterexample_of_increasing not_hypersmooth_increasingRelation

end
-- END COMPLETE MODULE Solutions.TheoremB

set_option autoImplicit false

open HypersmoothCounterexamples in
theorem solution :
    ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ Hypersmooth (BinaryFreeRelation ℓ) := by
  first
  | exact @HypersmoothCounterexamples.theoremB
  | apply @HypersmoothCounterexamples.theoremB <;> assumption

#print axioms solution
