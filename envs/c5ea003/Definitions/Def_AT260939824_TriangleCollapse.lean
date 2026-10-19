-- Prove2me | Definitions.Def_AT260939824_TriangleCollapse
-- name    : AT260939824_TriangleCollapse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:04:08.121925+00:00
-- url     : https://prove2.me/theorems/6a186c7d-a412-4c1c-aa11-798c613b1e16
-- title:
--   An explicit probability-simplex triangle collapse
-- statement:
--   For a finite vertex set $V$ and distinct vertices $a,b,c$, let $\mu$ be a probability mass and put $k=\min\{\mu(a),\mu(b)\}$. Define
--   $$C(\mu)=\mu-k\delta_a-k\delta_b+2k\delta_c,\qquad H(\mu,t)=(1-t)\mu+tC(\mu).$$
--   The collapse preserves probability masses and support in $\{a,b,c\}$, removes at least one of the positive $a,b$ coordinates, and fixes every mass with $\mu(a)=0$ or $\mu(b)=0$. In the maximum mass-coordinate metric, $C$ is $3$-Lipschitz, each homotopy track is $1$-Lipschitz, and $H$ is jointly $4$-Lipschitz for the maximum product metric. This is the local deformation used to remove fan diagonals.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/TriangleCollapse.lean, selected declaration lines 21-40, 42-47, 49-58, 60-70, 72-80, 106-108, 110-111, 113-115, 122-126, 128-131, 133-139, 141-156, 158-176; SHA-256 17af18d373c14e7b9421a363131e1cc1435737e20ae7dadce7603cfbc888487f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-!
# An explicit simplicial free-edge collapse

The two coordinates on a free edge lose their common minimum, and the
opposite vertex receives twice that amount. This is the literal PL
deformation onto the two retained sides of a triangle.
-/

namespace AbelianTargets.Probability

open scoped BigOperators NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def triangleCollapse (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : Probability V := by
  classical
  let k := min (p.mass a) (p.mass b)
  refine ⟨fun v => p.mass v + (if v = c then 2*k else 0) -
    (if v = a then k else 0) - (if v = b then k else 0), ?_, ?_⟩
  · intro v
    have hk : 0 ≤ k := le_min (p.nonneg a) (p.nonneg b)
    have hka : k ≤ p.mass a := min_le_left _ _
    have hkb : k ≤ p.mass b := min_le_right _ _
    by_cases ha : v = a
    · subst v; simp only [hac, hab, if_false, if_true]; linarith
    by_cases hb : v = b
    · subst v; simp only [hbc, Ne.symm hab, if_false, if_true]; linarith
    by_cases hc : v = c
    · subst v; simp only [Ne.symm hac, Ne.symm hbc, if_false, if_true]; linarith [p.nonneg c]
    · simp only [ha,hb,hc,if_false,add_zero,sub_zero]; exact p.nonneg v
  · rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    simp only [p.sum_one,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring

theorem triangleCollapse_mass (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (v : V) :
    (triangleCollapse a b c hab hac hbc p).mass v =
      p.mass v + (if v = c then 2*min (p.mass a) (p.mass b) else 0) -
        (if v = a then min (p.mass a) (p.mass b) else 0) -
          (if v = b then min (p.mass a) (p.mass b) else 0) := rfl

theorem triangleCollapse_fixes (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (h : p.mass a = 0 ∨ p.mass b = 0) :
    triangleCollapse a b c hab hac hbc p = p := by
  have hk : min (p.mass a) (p.mass b) = 0 := by
    rcases h with h | h
    · rw [h,min_eq_left (p.nonneg b)]
    · rw [h,min_eq_right (p.nonneg a)]
  ext v
  rw [triangleCollapse_mass,hk]
  simp

theorem triangleCollapse_supported (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (hp : p.SupportedOn ({a,b,c} : Set V)) :
    (triangleCollapse a b c hab hac hbc p).SupportedOn ({a,b,c} : Set V) := by
  apply supportedOn_iff_zero.mpr
  intro v hv
  have ha : v ≠ a := fun h => hv (by simp [h])
  have hb : v ≠ b := fun h => hv (by simp [h])
  have hc : v ≠ c := fun h => hv (by simp [h])
  rw [triangleCollapse_mass]
  simp only [ha,hb,hc,if_false,add_zero,sub_zero]
  exact supportedOn_iff_zero.mp hp v hv

theorem triangleCollapse_edge_removed (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) :
    (triangleCollapse a b c hab hac hbc p).mass a = 0 ∨
      (triangleCollapse a b c hab hac hbc p).mass b = 0 := by
  by_cases h : p.mass a ≤ p.mass b
  · left
    simp [triangleCollapse_mass,hac,hab,min_eq_left h]
  · right
    simp [triangleCollapse_mass,hbc,Ne.symm hab,min_eq_right (le_of_not_ge h)]



def triangleHomotopy (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (t : unitInterval) : Probability V :=
  mix p (triangleCollapse a b c hab hac hbc p) t

@[simp] theorem triangleHomotopy_zero (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : triangleHomotopy a b c hab hac hbc p 0 = p := mix_zero _ _

@[simp] theorem triangleHomotopy_one (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : triangleHomotopy a b c hab hac hbc p 1 =
      triangleCollapse a b c hab hac hbc p := mix_one _ _



theorem triangleHomotopy_fixes (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (h : p.mass a = 0 ∨ p.mass b = 0) (t : unitInterval) :
    triangleHomotopy a b c hab hac hbc p t = p := by
  unfold triangleHomotopy
  rw [triangleCollapse_fixes a b c hab hac hbc p h,mix_self]

theorem triangleHomotopy_supported (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (hp : p.SupportedOn ({a,b,c} : Set V)) (t : unitInterval) :
    (triangleHomotopy a b c hab hac hbc p t).SupportedOn ({a,b,c} : Set V) :=
  supportedOn_mix hp (triangleCollapse_supported a b c hab hac hbc p hp) t

theorem triangleHomotopy_track (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : LipschitzWith 1 (triangleHomotopy a b c hab hac hbc p) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  change dist (FixedSlots.mix p.mass (triangleCollapse a b c hab hac hbc p).mass r)
    (FixedSlots.mix p.mass (triangleCollapse a b c hab hac hbc p).mass s) ≤ _
  exact (FixedSlots.mix_lipschitz _ _ 1 (dist_le_one _ _)).dist_le_mul r s

theorem triangleCollapse_lipschitz (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LipschitzWith 3 (triangleCollapse a b c hab hac hbc) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (triangleCollapse a b c hab hac hbc p).mass
    (triangleCollapse a b c hab hac hbc q).mass ≤ 3*dist p q
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 3*dist p q)).mpr
  intro v
  rw [Real.dist_eq,triangleCollapse_mass,triangleCollapse_mass]
  have hv : |p.mass v-q.mass v| ≤ dist p q := dist_le_pi_dist p.mass q.mass v
  have hk : |min (p.mass a) (p.mass b)-min (q.mass a) (q.mass b)| ≤ dist p q :=
    (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (dist_le_pi_dist p.mass q.mass a) (dist_le_pi_dist p.mass q.mass b))
  rw [abs_le] at hv hk
  have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
  split_ifs <;> (try simp only [add_zero,sub_zero]) <;> rw [abs_le] <;> constructor <;> linarith

theorem triangleHomotopy_joint (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LipschitzWith 4 (fun z : Probability V × unitInterval => triangleHomotopy a b c hab hac hbc z.1 z.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨p,t⟩ ⟨q,s⟩
  have hspace : dist (triangleHomotopy a b c hab hac hbc p t)
      (triangleHomotopy a b c hab hac hbc q t) ≤ 3*dist p q := by
    have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
    exact FixedSlots.mix_dist_le_of_le (a := p.mass) (b := q.mass)
      (c := (triangleCollapse a b c hab hac hbc p).mass)
      (d := (triangleCollapse a b c hab hac hbc q).mass) (Δ := 3*dist p q)
      (by change dist p q ≤ 3*dist p q; linarith)
      ((triangleCollapse_lipschitz a b c hab hac hbc).dist_le_mul p q) t
  have htime := (triangleHomotopy_track a b c hab hac hbc q).dist_le_mul t s
  have hpq : dist p q ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_left _ _
  have hts : dist t s ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_right _ _
  have htri := dist_triangle (triangleHomotopy a b c hab hac hbc p t)
    (triangleHomotopy a b c hab hac hbc q t) (triangleHomotopy a b c hab hac hbc q s)
  norm_num at htime ⊢
  linarith

end
end AbelianTargets.Probability


