-- Prove2me | solution 1 for AbelianTargets.Probability.exists_commonPoint_close_of_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:04:17.143867+00:00
-- url     : https://prove2.me/submissions/d0d706a0-3f78-4961-9d35-1fea339e65d7

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SimplexMetricGluing
section
/-!
# A common-face estimate for finite probability simplices

Two nearby probability points have a normalized coordinatewise minimum
supported in both of their support sets. This quantitative fact permits
Lipschitz estimates on simplex charts to be glued without an intrinsic-metric
assumption. The image diameter handles pairs with disjoint supports.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]





theorem overlapMass_le_one (p q : Probability V) : overlapMass p q ≤ 1 := by
  calc
    overlapMass p q ≤ ∑ v, p.mass v := Finset.sum_le_sum fun v _ => min_le_left _ _
    _ = 1 := p.sum_one

theorem mass_dist_le (p q : Probability V) (v : V) :
    |p.mass v - q.mass v| ≤ dist p q := by
  exact (dist_le_pi_dist p.mass q.mass v)





theorem commonPoint_supportedOn_left (p q : Probability V) (h : 0 < overlapMass p q)
    {A : Set V} (hp : p.SupportedOn A) : (commonPoint p q h).SupportedOn A := by
  intro v hv
  have hv' : 0 < min (p.mass v) (q.mass v) :=
    (div_pos_iff_of_pos_right h).mp hv
  exact hp v (hv'.trans_le (min_le_left _ _))

theorem commonPoint_supportedOn_right (p q : Probability V) (h : 0 < overlapMass p q)
    {A : Set V} (hq : q.SupportedOn A) : (commonPoint p q h).SupportedOn A := by
  intro v hv
  have hv' : 0 < min (p.mass v) (q.mass v) :=
    (div_pos_iff_of_pos_right h).mp hv
  exact hq v (hv'.trans_le (min_le_right _ _))





end Probability





end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.SimplexDimensionBounds
section
/-!
# Common-face bounds depending on simplex dimension

The estimates depend on the number of vertices in a supporting simplex,
rather than on the total number of vertices of a growing interval carrier.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

theorem one_sub_overlapMass_le_of_supported (p q : Probability V)
    (s : Finset V) (hp : p.SupportedOn (s : Set V)) :
    1-overlapMass p q ≤ (s.card : ℝ)*dist p q := by
  classical
  have he : 1-overlapMass p q = ∑ v, (p.mass v-min (p.mass v) (q.mass v)) := by
    rw [Finset.sum_sub_distrib,p.sum_one]; rfl
  rw [he]
  calc
    _ ≤ ∑ v : V, if v ∈ s then dist p q else 0 := Finset.sum_le_sum fun v _ => by
      by_cases hv : v ∈ s
      · simp only [hv,if_true]
        have hd := mass_dist_le p q v
        by_cases h : p.mass v ≤ q.mass v
        · rw [min_eq_left h,sub_self]; exact dist_nonneg
        · rw [min_eq_right (le_of_not_ge h)]
          exact (abs_le.mp hd).2
      · have hz : p.mass v=0 := by
          apply le_antisymm _ (p.nonneg v)
          by_contra hh
          exact hv (hp v (lt_of_not_ge hh))
        simp only [hv,if_false,hz,min_eq_left (q.nonneg v),sub_self]
        exact le_rfl
    _ = (s.card : ℝ)*dist p q := by simp

theorem dist_commonPoint_le_loss (p q : Probability V) (h : 0<overlapMass p q) :
    dist p (commonPoint p q h) ≤ dist p q+(1-overlapMass p q) := by
  change dist p.mass (commonPoint p q h).mass ≤ _
  apply (dist_pi_le_iff (add_nonneg dist_nonneg (sub_nonneg.mpr (overlapMass_le_one p q)))).2
  intro v
  rw [Real.dist_eq,abs_le]
  have hm : 0 ≤ min (p.mass v) (q.mass v) := le_min (p.nonneg v) (q.nonneg v)
  have hs := overlapMass_le_one p q
  have hms : min (p.mass v) (q.mass v) ≤ overlapMass p q :=
    Finset.single_le_sum (fun w _ => le_min (p.nonneg w) (q.nonneg w)) (Finset.mem_univ v)
  have hmass : min (p.mass v) (q.mass v)/overlapMass p q ≤ 1 := (div_le_one h).2 hms
  have hmin : min (p.mass v) (q.mass v) ≤ min (p.mass v) (q.mass v)/overlapMass p q := by
    apply (le_div_iff₀ h).2
    exact mul_le_of_le_one_right hm hs
  have hdelta : p.mass v-min (p.mass v) (q.mass v) ≤ dist p q := by
    by_cases hv : p.mass v ≤ q.mass v
    · rw [min_eq_left hv,sub_self]; exact dist_nonneg
    · rw [min_eq_right (le_of_not_ge hv)]
      exact (abs_le.mp (mass_dist_le p q v)).2
  have hnorm : min (p.mass v) (q.mass v)/overlapMass p q-min (p.mass v) (q.mass v) ≤
      1-overlapMass p q := by
    have hid : min (p.mass v) (q.mass v)/overlapMass p q-min (p.mass v) (q.mass v) =
        (min (p.mass v) (q.mass v)/overlapMass p q)*(1-overlapMass p q) := by field_simp
    rw [hid]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hs) hmass
  change -(dist p q+(1-overlapMass p q)) ≤
      p.mass v-min (p.mass v) (q.mass v)/overlapMass p q ∧
      p.mass v-min (p.mass v) (q.mass v)/overlapMass p q ≤ _
  constructor <;> linarith [min_le_left (p.mass v) (q.mass v),dist_nonneg (x := p) (y := q)]

theorem dist_commonPoint_le_of_supported (p q : Probability V) (h : 0<overlapMass p q)
    (s : Finset V) (hp : p.SupportedOn (s : Set V)) :
    dist p (commonPoint p q h) ≤ ((s.card : ℝ)+1)*dist p q := by
  have h₁ := dist_commonPoint_le_loss p q h
  have h₂ := one_sub_overlapMass_le_of_supported p q s hp
  linarith



end Probability

end

end AbelianTargets

end

/-!
# Common-face bounds depending on simplex dimension

The estimates depend on the number of vertices in a supporting simplex,
rather than on the total number of vertices of a growing interval carrier.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped BigOperators NNReal
namespace AbelianTargets.Probability
end AbelianTargets.Probability
open AbelianTargets
open AbelianTargets.Probability
variable {V : Type*} [Fintype V]

theorem solution (p q : Probability V)
    (s t : Finset V) (hp : p.SupportedOn (s : Set V)) (hq : q.SupportedOn (t : Set V))
    (N : ℕ) (hs : s.card≤N) (ht : t.card≤N)
    (hclose : (N : ℝ)*dist p q < 1) :
    ∃ r : Probability V, r.SupportedOn (s : Set V) ∧ r.SupportedOn (t : Set V) ∧
      dist p r ≤ ((N : ℝ)+1)*dist p q ∧ dist q r ≤ ((N : ℝ)+1)*dist p q := by
  have hs' : (s.card : ℝ)≤N := by exact_mod_cast hs
  have ht' : (t.card : ℝ)≤N := by exact_mod_cast ht
  have hpos : 0<overlapMass p q := by
    have h := one_sub_overlapMass_le_of_supported p q s hp
    have hh := mul_le_mul_of_nonneg_right hs' (dist_nonneg (x := p) (y := q))
    linarith
  refine ⟨commonPoint p q hpos,commonPoint_supportedOn_left p q hpos hp,
    commonPoint_supportedOn_right p q hpos hq,?_,?_⟩
  · exact (dist_commonPoint_le_of_supported p q hpos s hp).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · have he : overlapMass q p=overlapMass p q := by unfold overlapMass; simp [min_comm]
    have he' : commonPoint q p (he.symm ▸ hpos)=commonPoint p q hpos := by
      ext v; simp [commonPoint,he,min_comm]
    have hh := dist_commonPoint_le_of_supported q p (he.symm ▸ hpos) t hq
    rw [he',dist_comm q p] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
