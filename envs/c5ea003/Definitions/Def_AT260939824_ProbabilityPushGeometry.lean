-- Prove2me | Definitions.Def_AT260939824_ProbabilityPushGeometry
-- name    : AT260939824_ProbabilityPushGeometry
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:49:00.717673+00:00
-- url     : https://prove2.me/theorems/33985081-81bc-4816-923c-3daedf4bd587
-- title:
--   Metric and composition laws for finite probability pushforward
-- statement:
--   Let $V,W,U$ be finite sets. Equip their probability simplexes with the maximum distance between mass coordinates, $d(\mu,\nu)=\max_v|\mu(v)-\nu(v)|$. For $f:V\to W$, define $(f_*\mu)(w)=\sum_{f(v)=w}\mu(v)$. The selected laws include
--   $$(g\circ f)_*=g_*\circ f_*,\qquad \operatorname{Lip}(f_*)\le |V|.$$
--   If $f$ is injective, $(f_*\mu)(f(v))=\mu(v)$ and $f_*$ is an isometry. If $f:V\to V$ fixes every vertex with positive $\mu$-mass, then $f_*\mu=\mu$. These laws transport carrier geometry without changing distances under injective vertex maps.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ProbabilityPushGeometry.lean, selected declaration lines 10-23, 25-39, 47-69, 71-75, 77-99; SHA-256 b6cede155227902bce3b328617635919c1d3b24febe02b97806feb8ca955ee2c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
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

namespace AbelianTargets.Probability
open scoped BigOperators NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W]

theorem push_eq_self (f : V → V) (p : Probability V)
    (hf : ∀ v, 0 < p.mass v → f v = v) : push f p = p := by
  ext w
  rw [push_mass]
  have he : (∑ v, if f v = w then p.mass v else 0) =
      ∑ v, if v = w then p.mass v else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : 0 < p.mass v
    · rw [hf v hp]
    · have hz : p.mass v = 0 := le_antisymm (le_of_not_gt hp) (p.nonneg v)
      simp [hz]
  rw [he]
  simp

theorem push_lipschitz (f : V → W) : LipschitzWith (Fintype.card V) (push f) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (push f p).mass (push f q).mass ≤ (Fintype.card V : ℝ)*dist p q
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ)*dist p q)).mpr
  intro w
  rw [Real.dist_eq,push_mass,push_mass,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ v, |(if f v = w then p.mass v else 0)-(if f v = w then q.mass v else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, dist p q := Finset.sum_le_sum (fun v _ => by
      by_cases h : f v = w
      · simpa only [h,if_true] using dist_le_pi_dist p.mass q.mass v
      · simp only [h,if_false,sub_self,abs_zero]; exact dist_nonneg)
    _ = _ := by simp



theorem push_comp {U : Type*} [Fintype U] (f : V → W) (g : W → U) (p : Probability V) :
    push g (push f p) = push (g ∘ f) p := by
  ext u
  simp only [push_mass]
  have he : (∑ w, if g w = u then ∑ v, if f v = w then p.mass v else 0 else 0) =
      ∑ w, ∑ v, if g w = u then (if f v = w then p.mass v else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs
    · rfl
    · simp
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have he' : (∑ w, if g w = u then (if f v = w then p.mass v else 0) else 0) =
      ∑ w, if w = f v then (if g (f v) = u then p.mass v else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : w = f v
    · subst w; simp
    · simp [h,Ne.symm h]
  rw [he']
  simp

theorem push_mass_of_injective (f : V → W) (hf : Function.Injective f) (p : Probability V) (v : V) :
    (push f p).mass (f v) = p.mass v := by
  rw [push_mass]
  simp only [hf.eq_iff]
  simp

theorem isometry_push (f : V → W) (hf : Function.Injective f) : Isometry (push f) := by
  apply Isometry.of_dist_eq
  intro p q
  apply le_antisymm
  · change dist (push f p).mass (push f q).mass ≤ dist p q
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro w
    by_cases hw : ∃ v, f v = w
    · obtain ⟨v,rfl⟩ := hw
      rw [push_mass_of_injective f hf, push_mass_of_injective f hf,Real.dist_eq]
      exact dist_le_pi_dist p.mass q.mass v
    · have hz (r : Probability V) : (push f r).mass w = 0 := by
        rw [push_mass]
        apply Finset.sum_eq_zero
        intro v hv
        simp [show f v ≠ w from fun h => hw ⟨v,h⟩]
      rw [hz p,hz q,dist_self]
      exact dist_nonneg
  · change dist p.mass q.mass ≤ dist (push f p) (push f q)
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro v
    rw [←push_mass_of_injective f hf p v,←push_mass_of_injective f hf q v]
    exact dist_le_pi_dist (push f p).mass (push f q).mass (f v)

end
end AbelianTargets.Probability


