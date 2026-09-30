-- Prove2me | solution 1 for Hirsch.positive_feedback_box_diameter_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T22:42:38.075061+00:00
-- url     : https://prove2.me/submissions/05df606c-7c8c-42eb-9e69-794b6be48926

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators

/-!
# Ordinary-edge routing from complementary affine bases

The hypotheses are linear equations and feasibility, not a graph-isomorphism
or a diameter premise. PolynomialPositiveFeedbackBoxes discharges them using
one positive vector. Verification receipts are maintained separately.
-/
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschPairedBases

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Vec (ι : Type*) := ι → ℝ

def pairedPoly (L : Vec ι →ₗ[ℝ] Vec ι) (b : Vec ι) : Set (Vec ι) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i, L x i ≤ b i}

def rhs (b : Vec ι) (s : ι → Bool) : Vec ι := fun i => if s i then b i else 0

/-- Each binary choice selects the lower equality x_i=0 or the upper equality
(Lx)_i=b_i. Every selected system is invertible, its solution is feasible,
and opposite equalities never hold at the same feasible point. -/
structure PairedBasisModel (L : Vec ι →ₗ[ℝ] Vec ι) (b : Vec ι) where
  basis : (ι → Bool) → Vec ι ≃ₗ[ℝ] Vec ι
  basis_spec : ∀ s x i, basis s x i = if s i then L x i else x i
  feasible : ∀ s, (basis s).symm (rhs b s) ∈ pairedPoly L b
  no_double : ∀ x ∈ pairedPoly L b, ∀ i, x i = 0 → L x i < b i

namespace PairedBasisModel
variable {L : Vec ι →ₗ[ℝ] Vec ι} {b : Vec ι}
variable (m : PairedBasisModel L b)

def point (s : ι → Bool) : Vec ι := (m.basis s).symm (rhs b s)

lemma point_mem (s : ι → Bool) : m.point s ∈ pairedPoly L b := m.feasible s

lemma point_equations (s : ι → Bool) (i : ι) :
    (if s i then L (m.point s) i else m.point s i) = rhs b s i := by
  rw [← m.basis_spec]
  exact congrFun ((m.basis s).apply_symm_apply (rhs b s)) i

lemma point_zero (s : ι → Bool) (i : ι) (hi : s i = false) : m.point s i = 0 := by
  simpa [hi, rhs] using m.point_equations s i

lemma point_upper (s : ι → Bool) (i : ι) (hi : s i = true) : L (m.point s) i = b i := by
  simpa [hi, rhs] using m.point_equations s i

lemma point_pos (s : ι → Bool) (i : ι) (hi : s i = true) : 0 < m.point s i := by
  have hp := (m.point_mem s).1 i
  have he := m.point_upper s i hi
  by_contra hn
  have hz : m.point s i = 0 := by linarith
  have hlt := m.no_double _ (m.point_mem s) i hz
  linarith

lemma point_injective : Function.Injective m.point := by
  intro s t he
  funext i
  by_contra hn
  cases hs : s i <;> cases ht : t i
  · exact hn (hs.trans ht.symm)
  · have hz := m.point_zero s i hs
    have hp := m.point_pos t i ht
    rw [he] at hz
    linarith
  · have hp := m.point_pos s i hs
    have hz := m.point_zero t i ht
    rw [he] at hp
    linarith
  · exact hn (hs.trans ht.symm)

/-- An equality at an interior point of a segment, bounded above at both
endpoints, is an equality at the first endpoint. -/
private lemma active_scalar {a c p q B : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hp : p ≤ B) (hq : q ≤ B) (he : a*p+c*q=B) : p = B := by
  by_contra hn
  have hlt : p < B := lt_of_le_of_ne hp hn
  have h1 := mul_lt_mul_of_pos_left hlt ha
  have h2 := mul_le_mul_of_nonneg_left hq hc
  have hscale : a*B+c*B=B := by rw [← add_mul, hac, one_mul]
  linarith

lemma pairedPoly_convex : Convex ℝ (pairedPoly L b) := by
  intro x hx y hy a c ha hc hac
  constructor
  · intro i
    change 0 ≤ a*x i+c*y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hc (hy.1 i))
  · intro i
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i) hc
    calc
      _ ≤ a*b i+c*b i := add_le_add h1 h2
      _ = b i := by rw [← add_mul, hac, one_mul]

lemma point_extreme (s : ι → Bool) : m.point s ∈ extremePoints ℝ (pairedPoly L b) := by
  refine ⟨m.point_mem s, ?_⟩
  intro p hp q hq hseg
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  apply (m.basis s).injective
  funext i
  rw [m.basis_spec, m.basis_spec]
  cases hs : s i
  · have he0 := m.point_zero s i hs
    have he := congrFun hcomb i
    change a*p i+c*q i=m.point s i at he
    have hp0 : p i = 0 := by
      have ht := active_scalar ha hc.le hac (neg_nonpos.mpr (hp.1 i))
        (neg_nonpos.mpr (hq.1 i)) (show a*(-p i)+c*(-q i)=0 by nlinarith)
      linarith
    simpa [hs, hp0, he0]
  · have hu := m.point_upper s i hs
    have he := congrFun (congrArg L hcomb) i
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    have ht := active_scalar ha hc.le hac (hp.2 i) (hq.2 i) (he.trans hu)
    simpa [hs, ht, hu]

/-- Generic finite perturbation lemma, parallel to the repository's Euclidean
vertex-span proof. No topology or imported theorem placeholder is needed. -/
private lemma finite_linear_vertex_span {R E : Type*} [Fintype R]
    [AddCommGroup E] [Module ℝ E]
    (a : R → E →ₗ[ℝ] ℝ) (B : R → ℝ)
    (x : E) (hx : x ∈ extremePoints ℝ {z | ∀ r, a r z ≤ B r})
    (y : E) (horth : ∀ r, a r x = B r → a r y = 0) : y = 0 := by
  classical
  have hlocal : ∀ r : R, ∃ t : ℝ, 0 < t ∧ t * |a r y| ≤ B r - a r x := by
    intro r
    by_cases hr : a r x = B r
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth r hr, abs_zero, mul_zero, hr, sub_self]
    · have hs : 0 < B r - a r x := sub_pos.mpr (lt_of_le_of_ne (hx.1 r) hr)
      have hd : 0 < |a r y| + 1 := by positivity
      let t := (B r-a r x)/(|a r y|+1)
      have ht : 0 < t := div_pos hs hd
      have he : t*(|a r y|+1)=B r-a r x := div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t,ht,by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset R, ∃ t : ℝ, 0 < t ∧ ∀ r ∈ S, t ≤ e r := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert r S hr ih =>
      obtain ⟨t,ht,hte⟩ := ih
      refine ⟨min (e r) t,lt_min (hepos r) ht,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with heq | hj
      · subst j; exact min_le_left _ _
      · exact (min_le_right _ _).trans (hte j hj)
  obtain ⟨t,ht,hte⟩ := huniform Finset.univ
  have hbudget : ∀ r, t*|a r y| ≤ B r-a r x := fun r =>
    (mul_le_mul_of_nonneg_right (hte r (Finset.mem_univ r)) (abs_nonneg _)).trans (hebound r)
  have hp : ∀ r, a r (x+t•y) ≤ B r := by
    intro r
    simp only [map_add,map_smul,smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (le_abs_self (a r y)) ht.le
    linarith [hbudget r]
  have hm : ∀ r, a r (x-t•y) ≤ B r := by
    intro r
    simp only [map_sub,map_smul,smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (neg_le_abs (a r y)) ht.le
    linarith [hbudget r]
  have hmid : x ∈ openSegment ℝ (x+t•y) (x-t•y) := by
    refine ⟨(1/2:ℝ),(1/2:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have heq := hx.2 hp hm hmid
  have hz : t•y=0 := by
    have h := congrArg (fun z => z-x) heq
    simpa using h
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt ht)

def lowerRow (i : ι) : Vec ι →ₗ[ℝ] ℝ where
  toFun x := -x i
  map_add' x y := by simp [add_comm]
  map_smul' a x := by simp

def upperRow (i : ι) : Vec ι →ₗ[ℝ] ℝ where
  toFun x := L x i
  map_add' x y := by simp
  map_smul' a x := by simp

/-- No extra vertices are silently omitted. A vertex with both inequalities
slack in one pair admits a nonzero two-sided feasible perturbation. -/
theorem extreme_eq_point (x : Vec ι) (hx : x ∈ extremePoints ℝ (pairedPoly L b)) :
    ∃ s, x = m.point s := by
  classical
  let s : ι → Bool := fun i => decide (L x i = b i)
  have hzero : ∀ i, s i = false → x i = 0 := by
    intro i hi
    have hnot : L x i ≠ b i := by simpa [s] using hi
    by_contra hxi
    let y := (m.basis s).symm (Pi.single i 1)
    have hby : m.basis s y = Pi.single i 1 := (m.basis s).apply_symm_apply _
    let a : Sum ι ι → Vec ι →ₗ[ℝ] ℝ := Sum.elim lowerRow (upperRow (L:=L))
    let B : Sum ι ι → ℝ := Sum.elim (fun _ => 0) b
    have hP : {z | ∀ r, a r z ≤ B r} = pairedPoly L b := by
      ext z
      simp [a,B,pairedPoly,lowerRow,upperRow,Sum.forall,neg_nonpos]
    have hx' : x ∈ extremePoints ℝ {z | ∀ r, a r z ≤ B r} := by rwa [hP]
    have hy0 : y = 0 := by
      apply finite_linear_vertex_span a B x hx' y
      intro r hr
      cases r with
      | inl j =>
        have hxj : x j = 0 := by change -x j=0 at hr; linarith
        have hji : j ≠ i := by intro he; subst j; exact hxi hxj
        have hs : s j = false := by
          have hlt := m.no_double x hx.1 j hxj
          simp [s,ne_of_lt hlt]
        have hj := congrFun hby j
        rw [m.basis_spec] at hj
        have hz : y j=0 := by simpa [hs,Pi.single_apply,hji] using hj
        change -y j=0
        simp [hz]
      | inr j =>
        have hxj : L x j=b j := hr
        have hji : j ≠ i := by intro he; subst j; exact hnot hxj
        have hs : s j=true := by simp [s,hxj]
        have hj := congrFun hby j
        rw [m.basis_spec] at hj
        change L y j=0
        simpa [hs,Pi.single_apply,hji] using hj
    have hbad := congrFun hby i
    rw [hy0,map_zero] at hbad
    norm_num at hbad
  refine ⟨s,?_⟩
  apply (m.basis s).injective
  rw [show m.basis s (m.point s)=rhs b s from (m.basis s).apply_symm_apply _]
  funext i
  rw [m.basis_spec]
  cases hi : s i
  · simpa [hi,rhs] using hzero i hi
  · have ht : L x i=b i := by simpa [s] using hi
    simp [hi,rhs,ht]

/-- The equations retained in a one-bit change define an extreme subset. -/
lemma shared_equations_extreme (s : ι → Bool) (i : ι) :
    IsExtreme ℝ (pairedPoly L b)
      {z | z ∈ pairedPoly L b ∧ ∀ j, j ≠ i → m.basis s z j=rhs b s j} := by
  refine ⟨fun z hz => hz.1,?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp,?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  intro j hji
  have hez := hz.2 j hji
  rw [m.basis_spec] at hez
  rw [m.basis_spec]
  cases hs : s j
  · have hz0 : z j=0 := by simpa [hs,rhs] using hez
    have he := congrFun hcomb j
    change a*p j+c*q j=z j at he
    have ht := active_scalar ha hc.le hac (neg_nonpos.mpr (hp.1 j))
      (neg_nonpos.mpr (hq.1 j)) (show a*(-p j)+c*(-q j)=0 by nlinarith)
    have hp0 : p j=0 := by linarith
    simp [hs,rhs,hp0]
  · have hzt : L z j=b j := by simpa [hs,rhs] using hez
    have he := congrFun (congrArg L hcomb) j
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he
    have ht := active_scalar ha hc.le hac (hp.2 j) (hq.2 j) (he.trans hzt)
    simp [hs,rhs,ht]

/-- A binary pivot is an ORDINARY EDGE. Other coordinates may move too; this
is not a coordinate-axis step or a circuit step. -/
theorem point_adj_update (s : ι → Bool) (i : ι) (hi : s i=false) :
    Adj (pairedPoly L b) (m.point s) (m.point (Function.update s i true)) := by
  classical
  let t := Function.update s i true
  let p := m.point s
  let q := m.point t
  have hp := m.point_mem s
  have hq := m.point_mem t
  have hp0 : p i=0 := m.point_zero s i hi
  have hqpos : 0<q i := m.point_pos t i (by simp [t])
  have hqtop : L q i=b i := m.point_upper t i (by simp [t])
  have hpstrict : L p i<b i := m.no_double p hp i hp0
  let F : Set (Vec ι) :=
    {z | z ∈ pairedPoly L b ∧ ∀ j, j ≠ i → m.basis s z j=rhs b s j}
  have hpF : p ∈ F := by
    refine ⟨hp,?_⟩
    intro j _
    exact congrFun ((m.basis s).apply_symm_apply _) j
  have hqF : q ∈ F := by
    refine ⟨hq,?_⟩
    intro j hji
    have ht := m.point_equations t j
    rw [m.basis_spec]
    simpa [q,t,Function.update_of_ne hji,rhs] using ht
  have hFext : IsExtreme ℝ (pairedPoly L b) F := m.shared_equations_extreme s i
  have hFseg : F = segment ℝ p q := by
    apply Set.Subset.antisymm
    · intro z hz
      let theta : ℝ := z i/q i
      have htheta0 : 0≤theta := div_nonneg (hz.1.1 i) hqpos.le
      have hthetaq : theta*q i=z i := div_mul_cancel₀ _ (ne_of_gt hqpos)
      have hzcomb : (1-theta)•p+theta•q=z := by
        apply (m.basis s).injective
        funext j
        by_cases hji : j=i
        · subst j
          simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
          rw [m.basis_spec,m.basis_spec,m.basis_spec]
          simp [hi,hp0,hthetaq]
        · have h1 := hpF.2 j hji
          have h2 := hqF.2 j hji
          have h3 := hz.2 j hji
          simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
          rw [h1,h2,h3]
          ring
      have hl := congrFun (congrArg L hzcomb) i
      simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hl
      have htheta1 : theta≤1 := by
        have hbound := hz.1.2 i
        rw [hqtop] at hl
        nlinarith
      exact ⟨1-theta,theta,sub_nonneg.mpr htheta1,htheta0,by ring,hzcomb⟩
    · intro z hz
      obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hz
      refine ⟨?_,?_⟩
      · rw [←hcomb]
        exact pairedPoly_convex hp hq ha hc hac
      · intro j hji
        rw [←hcomb]
        simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
        rw [hpF.2 j hji,hqF.2 j hji, ← add_mul, hac, one_mul]
  refine ⟨?_,?_⟩
  · intro he
    have he' := congrFun he i
    change p i=q i at he'
    linarith
  · change IsExtreme ℝ (pairedPoly L b) (segment ℝ p q)
    rwa [hFseg] at hFext

lemma point_adj_of_single_change (s t : ι → Bool) (i : ι)
    (hi : s i ≠ t i) (hrest : ∀ j, j ≠ i → s j=t j) :
    Adj (pairedPoly L b) (m.point s) (m.point t) := by
  classical
  cases hs : s i <;> cases ht : t i
  · exact False.elim (hi (hs.trans ht.symm))
  · have he : Function.update s i true=t := by
      funext j
      by_cases hj : j=i
      · subst j; simp [ht]
      · simp [hj,hrest j hj]
    simpa [he] using m.point_adj_update s i hs
  · have he : Function.update t i true=s := by
      funext j
      by_cases hj : j=i
      · subst j; simp [hs]
      · simp [hj,(hrest j hj).symm]
    have h := m.point_adj_update t i ht
    rw [he] at h
    exact ⟨h.1.symm,by rw [segment_symm]; exact h.2⟩
  · exact False.elim (hi (hs.trans ht.symm))

end PairedBasisModel

/-- Process the coordinate labels in order, changing each at most once. -/
theorem paired_basis_diamLE {d : ℕ}
    {L : Vec (Fin d) →ₗ[ℝ] Vec (Fin d)} {b : Vec (Fin d)}
    (m : PairedBasisModel L b) : DiamLE (pairedPoly L b) d := by
  intro x hx y hy
  obtain ⟨s,rfl⟩ := m.extreme_eq_point x hx
  obtain ⟨t,rfl⟩ := m.extreme_eq_point y hy
  let sig : ℕ → Fin d → Bool := fun k j => if j.val<k then t j else s j
  have h0 : sig 0=s := by funext j; simp [sig]
  have hd : sig d=t := by funext j; simp [sig,j.isLt]
  refine ⟨fun k => m.point (sig k),by simpa only [h0],by simpa only [hd],?_⟩
  intro k hk
  let i : Fin d := ⟨k,hk⟩
  have hrest : ∀ j : Fin d, j≠i → sig k j=sig (k+1) j := by
    intro j hj
    have hval : j.val≠k := by intro he; apply hj; exact Fin.ext he
    by_cases hlt : j.val<k
    · have hlt' : j.val<k+1 := by omega
      simp [sig,hlt,hlt']
    · have hlt' : ¬j.val<k+1 := by omega
      simp [sig,hlt,hlt']
  by_cases he : sig k i=sig (k+1) i
  · left
    change m.point (sig k) = m.point (sig (k+1))
    apply congrArg m.point
    funext j
    by_cases hj : j=i
    · simpa [hj] using he
    · exact hrest j hj
  · right
    exact m.point_adj_of_single_change _ _ i he hrest

end HirschPairedBases
end

/-!
# Coupled boxes with nonnegative feedback

One checkable vector w>0, Cw<w replaces exponentially many complementary-basis
checks. No acyclicity, small row sum, projective separator, recursive diameter
input, or small-excess theorem is assumed. See the separate verification receipts.
-/
open Set Hirsch HirschPairedBases
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschPositiveBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted maximum principle. This is the nonsingular M-matrix argument
in elementary ordered-linear form; it is not claimed as new classical theory. -/
theorem nonpos_of_le_positive_map
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (z : Vec ι) (hz : z ≤ C z) : z ≤ 0 := by
  classical
  by_contra hn
  have hn' : ¬ ∀ i, z i≤0 := hn
  push_neg at hn'
  obtain ⟨i,hi⟩ := hn'
  obtain ⟨j,_hj,hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset ι) (fun k => z k/w k) ⟨i,Finset.mem_univ i⟩
  let t : ℝ := z j/w j
  have ht : 0<t := (div_pos hi (hw i)).trans_le (hmax i (Finset.mem_univ i))
  have hbound : z ≤ t•w := by
    intro k
    change z k≤t*w k
    apply (div_le_iff₀ (hw k)).mp
    exact hmax k (Finset.mem_univ k)
  have hC := hmono hbound j
  have hstrict := mul_lt_mul_of_pos_left (hcw j) ht
  have he : t*w j=z j := div_mul_cancel₀ _ (ne_of_gt (hw j))
  simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hC
  have hzj := hz j
  linarith

lemma nonneg_of_id_sub_nonneg
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (z : Vec ι) (hz : 0 ≤ (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) z) : 0 ≤ z := by
  have hn : -z ≤ C (-z) := by
    intro i
    have hi := hz i
    change 0≤z i-C z i at hi
    simp only [map_neg,Pi.neg_apply]
    linarith
  have h := nonpos_of_le_positive_map C hmono w hw hcw (-z) hn
  intro i
  have hi := h i
  change -z i≤0 at hi
  change 0 ≤ z i
  linarith

lemma id_sub_injective
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) :
    Function.Injective (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) := by
  intro x y hxy
  have hz : (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) (x-y)=0 := by
    rw [map_sub,hxy,sub_self]
  have hp := nonneg_of_id_sub_nonneg C hmono w hw hcw (x-y) (by rw [hz])
  have hm := nonneg_of_id_sub_nonneg C hmono w hw hcw (-(x-y))
    (by rw [map_neg,hz,neg_zero])
  funext i
  have hpi := hp i
  have hmi := hm i
  change 0≤x i-y i at hpi
  change 0≤-(x i-y i) at hmi
  linarith

def inverseBasis
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) :
    Vec ι ≃ₗ[ℝ] Vec ι :=
  LinearEquiv.ofBijective (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _)
    ⟨id_sub_injective C hmono w hw hcw,
      LinearMap.surjective_of_injective (id_sub_injective C hmono w hw hcw)⟩

def maskMap (s : ι → Bool) : Vec ι →ₗ[ℝ] Vec ι where
  toFun x i := if s i then x i else 0
  map_add' x y := by funext i; cases hs : s i <;> simp [hs]
  map_smul' a x := by funext i; cases hs : s i <;> simp [hs]

lemma masked_monotone (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C) (s : ι → Bool) :
    Monotone ((maskMap s).comp C) := by
  intro x y hxy i
  change (if s i then C x i else 0) ≤ (if s i then C y i else 0)
  cases s i
  · exact le_rfl
  · exact hmono hxy i

lemma masked_weight (C : Vec ι →ₗ[ℝ] Vec ι)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) (s : ι → Bool) :
    ∀ i, ((maskMap s).comp C) w i<w i := by
  intro i
  change (if s i then C w i else 0)<w i
  cases s i
  · exact hw i
  · exact hcw i

/-- ALL complementary bases, positive solutions and disjoint pairs follow
from the single weighted positivity witness. -/
def positiveFeedbackModel
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec ι) (hb : ∀ i, 0<b i) : PairedBasisModel (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) b := by
  let basis := fun s => inverseBasis ((maskMap s).comp C)
    (masked_monotone C hmono s) w hw (masked_weight C w hw hcw s)
  have hspec : ∀ s x i, basis s x i = if s i then (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) x i else x i := by
    intro s x i
    change x i-(if s i then C x i else 0)=_
    cases hs : s i <;> simp [hs]
  refine ⟨basis,hspec,?_,?_⟩
  · intro s
    let x := (basis s).symm (rhs b s)
    have he : (LinearMap.id-(maskMap s).comp C : Vec _ →ₗ[ℝ] Vec _) x=rhs b s :=
      (basis s).apply_symm_apply _
    have hnonneg : 0≤x := by
      apply nonneg_of_id_sub_nonneg ((maskMap s).comp C)
        (masked_monotone C hmono s) w hw (masked_weight C w hw hcw s) x
      rw [he]
      intro i
      simp only [rhs]
      cases s i
      · exact le_rfl
      · exact (hb i).le
    have hCx : 0≤C x := by simpa only [map_zero] using hmono hnonneg
    refine ⟨hnonneg,?_⟩
    intro i
    have hei := congrFun he i
    change x i-(if s i then C x i else 0)=rhs b s i at hei
    change x i-C x i≤b i
    cases hs : s i
    · have hx0 : x i=0 := by simpa [hs,rhs] using hei
      have hc : (0 : ℝ) ≤ C x i := hCx i
      rw [hx0]
      linarith [hb i]
    · have hxtop : x i-C x i=b i := by simpa [hs,rhs] using hei
      exact hxtop.le
  · intro x hx i hxi
    have hCx : 0≤C x := by
      have h := hmono (show (0 : Vec ι) ≤ x from hx.1)
      simpa only [map_zero] using h
    change x i-C x i<b i
    rw [hxi]
    have hci : (0 : ℝ) ≤ C x i := hCx i
    linarith [hb i]

/-- Direct ordinary-edge diameter theorem; no recursive geometric input. -/
theorem positive_feedback_diamLE {d : ℕ}
    (C : Vec (Fin d) →ₗ[ℝ] Vec (Fin d)) (hmono : Monotone C)
    (w : Vec (Fin d)) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec (Fin d)) (hb : ∀ i, 0<b i) :
    DiamLE (pairedPoly (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) b) d :=
  paired_basis_diamLE (positiveFeedbackModel C hmono w hw hcw b hb)

/-- The all-upper solution is a coordinatewise upper bound for the entire
polytope, not just for its vertices. -/
theorem positive_feedback_le_top
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec ι) (hb : ∀ i, 0<b i)
    (x : Vec ι) (hx : x ∈ pairedPoly (LinearMap.id-C : Vec _ →ₗ[ℝ] Vec _) b) :
    x ≤ (positiveFeedbackModel C hmono w hw hcw b hb).point (fun _ => true) := by
  let m := positiveFeedbackModel C hmono w hw hcw b hb
  let v := m.point (fun _ => true)
  have hz : x-v ≤ C (x-v) := by
    intro i
    have hv := m.point_upper (fun _ => true) i rfl
    have hx' := hx.2 i
    change v i-C v i=b i at hv
    change x i-C x i≤b i at hx'
    simp only [map_sub,Pi.sub_apply]
    linarith
  have h := nonpos_of_le_positive_map C hmono w hw hcw (x-v) hz
  intro i
  have hi := h i
  change x i-v i≤0 at hi
  exact sub_nonpos.mp hi

def matrixMap (C : ι → ι → ℝ) : Vec ι →ₗ[ℝ] Vec ι where
  toFun x i := ∑ j, C i j*x j
  map_add' x y := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' a x := by funext i; simp [Finset.mul_sum,mul_assoc,mul_left_comm]

lemma matrixMap_monotone (C : ι → ι → ℝ) (hC : ∀ i j, 0≤C i j) :
    Monotone (matrixMap C) := by
  intro x y hxy i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hC i j))

/-- Explicit finite matrix criterion consumed by the rational checker. -/
theorem matrix_positive_feedback_diamLE {d : ℕ}
    (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0≤C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0<b i) (hw : ∀ i, 0<w i)
    (hcw : ∀ i, (∑ j, C i j*w j)<w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0≤x i) ∧ ∀ i, x i≤b i+∑ j, C i j*x j} d := by
  have h := positive_feedback_diamLE (matrixMap C) (matrixMap_monotone C hC) w hw hcw b hb
  have he : pairedPoly (LinearMap.id-matrixMap C : Vec _ →ₗ[ℝ] Vec _) b =
      {x : Fin d → ℝ | (∀ i, 0≤x i) ∧ ∀ i, x i≤b i+∑ j, C i j*x j} := by
    ext x
    simp only [pairedPoly,Set.mem_setOf_eq]
    constructor <;> rintro ⟨hx,hbnd⟩ <;> refine ⟨hx,?_⟩ <;> intro i
    · have hi := hbnd i
      change x i-(∑ j, C i j*x j)≤b i at hi
      linarith
    · have hi := hbnd i
      change x i-(∑ j, C i j*x j)≤b i
      linarith
  rwa [he] at h

end HirschPositiveBoxes
end

theorem solution {d : ℕ} (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0 < b i) (hw : ∀ i, 0 < w i)
    (hcw : ∀ i, (∑ j, C i j * w j) < w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0 ≤ x i) ∧
      ∀ i, x i ≤ b i + ∑ j, C i j * x j} d := by
  exact HirschPositiveBoxes.matrix_positive_feedback_diamLE C hC b w hb hw hcw
