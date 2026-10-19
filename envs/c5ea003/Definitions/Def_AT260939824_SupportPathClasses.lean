-- Prove2me | Definitions.Def_AT260939824_SupportPathClasses
-- name    : AT260939824_SupportPathClasses
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:20:47.385814+00:00
-- url     : https://prove2.me/theorems/8f0d7ebf-f6e0-481b-a501-16084c3b1aa0
-- title:
--   Path-class relations in products of simplex faces
-- statement:
--   For a finite graph $H$, use left and right affine interpolation paths in its support complex whenever the opposite shore is fixed and compatibility holds. Their relative homotopy classes satisfy concatenation cancellation of intermediate points, reversal identities, and constant-path identities. If all four corners $(p,q),(r,q),(p,s),(r,s)$ are compatible, the two coordinate routes commute:
--   $$[L_{p\to r;q}]\,[R_{q\to s;r}]
--   =[R_{q\to s;p}]\,[L_{p\to r;s}].$$
--   The selected laws also express associativity with a following path and reversal of a concatenation. In particular the canonical realization of an alternating four-edge closed walk in the bipartite double cover is nullhomotopic, including the detours arising from chosen neighbors.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportPathClasses.lean, selected declaration lines 70-71, 73-74, 76-79, 81-84, 86-90, 92-96, 98-105, 107-114, 116-140, 142-149, 151-157, 159-165, 167-176, 178-185, 187-191, 193-197, 199-201, 203-235; SHA-256 1df4f98788bbd57ebad7477dd3045ca05d0b56c6d6d1adece55ebbaac5db0164. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
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

/-!
# Path-class algebra of the support complex

The fixed-shore paths compose uniquely, reverse correctly, and commute
across every product of two simplex faces.  This is the concrete topological
square relation in Lemma 6.2 of arXiv:2609.39824.
-/

open scoped unitInterval

namespace AbelianTargets.SupportPair

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)













abbrev leftClass {p r q : Probability V} (hp : Compatible H p q) (hr : Compatible H r q) :=
  Path.Homotopic.Quotient.mk (leftPath H hp hr)

abbrev rightClass {p q s : Probability V} (hq : Compatible H p q) (hs : Compatible H p s) :=
  Path.Homotopic.Quotient.mk (rightPath H hq hs)

theorem leftClass_trans {p r s q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) (hs : Compatible H s q) :
    Path.Homotopic.Quotient.trans (leftClass H hp hr) (leftClass H hr hs) = leftClass H hp hs :=
  Path.Homotopic.Quotient.eq.mpr (leftPath_trans_homotopic H hp hr hs)

theorem rightClass_trans {p q r s : Probability V}
    (hq : Compatible H p q) (hr : Compatible H p r) (hs : Compatible H p s) :
    Path.Homotopic.Quotient.trans (rightClass H hq hr) (rightClass H hr hs) = rightClass H hq hs :=
  Path.Homotopic.Quotient.eq.mpr (rightPath_trans_homotopic H hq hr hs)

theorem leftClass_symm {p r q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) :
    Path.Homotopic.Quotient.symm (leftClass H hp hr) = leftClass H hr hp := by
  apply Path.Homotopic.Quotient.eq.mpr
  exact ⟨fixedRightHomotopy H _ _ q (fun _ => rfl) (fun _ => rfl)⟩

theorem rightClass_symm {p q s : Probability V}
    (hq : Compatible H p q) (hs : Compatible H p s) :
    Path.Homotopic.Quotient.symm (rightClass H hq hs) = rightClass H hs hq := by
  apply Path.Homotopic.Quotient.eq.mpr
  exact ⟨fixedLeftHomotopy H _ _ p (fun _ => rfl) (fun _ => rfl)⟩

@[simp] theorem leftClass_self {p q : Probability V} (hp : Compatible H p q) :
    leftClass H hp hp = Path.Homotopic.Quotient.refl (⟨(p,q), hp⟩ : SupportPair H) := by
  change Path.Homotopic.Quotient.mk (leftPath H hp hp) = Path.Homotopic.Quotient.mk _
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [leftPath]

@[simp] theorem rightClass_self {p q : Probability V} (hp : Compatible H p q) :
    rightClass H hp hp = Path.Homotopic.Quotient.refl (⟨(p,q), hp⟩ : SupportPair H) := by
  change Path.Homotopic.Quotient.mk (rightPath H hp hp) = Path.Homotopic.Quotient.mk _
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [rightPath]

/-- The two routes around a rectangle in a product-simplex carrier are
homotopic with endpoints fixed. -/
theorem rectangle_paths_homotopic {p r q s : Probability V}
    (hpq : Compatible H p q) (hps : Compatible H p s)
    (hrq : Compatible H r q) (hrs : Compatible H r s) :
    ((leftPath H hpq hrq).trans (rightPath H hrq hrs)).Homotopic
      ((rightPath H hpq hps).trans (leftPath H hps hrs)) := by
  let A : Set V := {a | 0 < p.mass a ∨ 0 < r.mass a}
  let B : Set V := {b | 0 < q.mass b ∨ 0 < s.mass b}
  have hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := by
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hpq a b ha hb
    · exact hps a b ha hb
    · exact hrq a b ha hb
    · exact hrs a b ha hb
  have hpA : p.SupportedOn A := fun _ ha => Or.inl ha
  have hrA : r.SupportedOn A := fun _ ha => Or.inr ha
  have hqB : q.SupportedOn B := fun _ hb => Or.inl hb
  have hsB : s.SupportedOn B := fun _ hb => Or.inr hb
  exact ⟨carrierHomotopy H hAB _ _
    (inCarrier_trans H _ _ (leftPath_inCarrier H _ _ hpA hrA hqB)
      (rightPath_inCarrier H _ _ hrA hqB hsB))
    (inCarrier_trans H _ _ (rightPath_inCarrier H _ _ hpA hqB hsB)
      (leftPath_inCarrier H _ _ hpA hrA hsB))⟩

/-- Commutation of the two simplex factors at the level of genuine path
homotopy classes. -/
theorem rectangle_classes_commute {p r q s : Probability V}
    (hpq : Compatible H p q) (hps : Compatible H p s)
    (hrq : Compatible H r q) (hrs : Compatible H r s) :
    Path.Homotopic.Quotient.trans (leftClass H hpq hrq) (rightClass H hrq hrs) =
      Path.Homotopic.Quotient.trans (rightClass H hpq hps) (leftClass H hps hrs) :=
  Path.Homotopic.Quotient.eq.mpr (rectangle_paths_homotopic H hpq hps hrq hrs)

theorem leftClass_trans_assoc {p r s q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) (hs : Compatible H s q)
    {z : SupportPair H} (R : Path.Homotopic.Quotient (⟨(s,q),hs⟩ : SupportPair H) z) :
    Path.Homotopic.Quotient.trans (leftClass H hp hr)
        (Path.Homotopic.Quotient.trans (leftClass H hr hs) R) =
      Path.Homotopic.Quotient.trans (leftClass H hp hs) R := by
  rw [← Path.Homotopic.Quotient.trans_assoc, leftClass_trans]

theorem rightClass_trans_assoc {p q r s : Probability V}
    (hq : Compatible H p q) (hr : Compatible H p r) (hs : Compatible H p s)
    {z : SupportPair H} (R : Path.Homotopic.Quotient (⟨(p,s),hs⟩ : SupportPair H) z) :
    Path.Homotopic.Quotient.trans (rightClass H hq hr)
        (Path.Homotopic.Quotient.trans (rightClass H hr hs) R) =
      Path.Homotopic.Quotient.trans (rightClass H hq hs) R := by
  rw [← Path.Homotopic.Quotient.trans_assoc, rightClass_trans]

theorem rectangle_classes_commute_assoc {p r q s : Probability V}
    (hpq : Compatible H p q) (hps : Compatible H p s)
    (hrq : Compatible H r q) (hrs : Compatible H r s)
    {z : SupportPair H} (R : Path.Homotopic.Quotient (⟨(r,s),hrs⟩ : SupportPair H) z) :
    Path.Homotopic.Quotient.trans (leftClass H hpq hrq)
        (Path.Homotopic.Quotient.trans (rightClass H hrq hrs) R) =
      Path.Homotopic.Quotient.trans (rightClass H hpq hps)
        (Path.Homotopic.Quotient.trans (leftClass H hps hrs) R) := by
  rw [← Path.Homotopic.Quotient.trans_assoc, rectangle_classes_commute H hpq hps hrq hrs,
    Path.Homotopic.Quotient.trans_assoc]

theorem quotient_symm_trans {X : Type*} [TopologicalSpace X] {a b c : X}
    (P : Path.Homotopic.Quotient a b) (Q : Path.Homotopic.Quotient b c) :
    Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.trans P Q) =
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm Q) (Path.Homotopic.Quotient.symm P) := by
  induction P using Path.Homotopic.Quotient.ind with | mk P =>
  induction Q using Path.Homotopic.Quotient.ind with | mk Q =>
  simp only [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
    Path.trans_symm]

@[simp] theorem quotient_symm_symm {X : Type*} [TopologicalSpace X] {a b : X}
    (P : Path.Homotopic.Quotient a b) :
    Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.symm P) = P := by
  induction P using Path.Homotopic.Quotient.ind with | mk P =>
  simp only [← Path.Homotopic.Quotient.mk_symm, Path.symm_symm]

@[simp] theorem quotient_refl_symm {X : Type*} [TopologicalSpace X] (a : X) :
    Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.refl a) =
      Path.Homotopic.Quotient.refl a := by
  change Path.Homotopic.Quotient.mk (Path.refl a).symm = Path.Homotopic.Quotient.mk (Path.refl a)
  rw [Path.refl_symm]

abbrev doubleClass {u u' v v' : V}
    (hu : H.Adj u u') (huv : H.Adj u v) (hv : H.Adj v' v) :=
  Path.Homotopic.Quotient.mk (doubleEdgePath H hu huv hv)

/-- The canonical realization of an alternating double-cover four-walk is
nullhomotopic, including its chosen-neighbor detours. -/
theorem doubleCover_four_null {v w x y v' w' x' y' : V}
    (hv : H.Adj v v') (hw : H.Adj w w') (hx : H.Adj x x') (hy : H.Adj y y')
    (hvw : H.Adj v w) (hxw : H.Adj x w) (hxy : H.Adj x y) (hvy : H.Adj v y) :
    Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans (doubleClass H hv hvw hw.symm)
          (Path.Homotopic.Quotient.symm (doubleClass H hx hxw hw.symm)))
        (doubleClass H hx hxy hy.symm))
      (Path.Homotopic.Quotient.symm (doubleClass H hv hvy hy.symm)) =
      Path.Homotopic.Quotient.refl (vertex H hv) := by
  simp only [doubleClass, doubleEdgePath]
  change Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans (rightClass H (compatible_dirac H hv) (compatible_dirac H hvw))
          (leftClass H (compatible_dirac H hvw) (compatible_dirac H hw.symm)))
        (Path.Homotopic.Quotient.symm
          (Path.Homotopic.Quotient.trans (rightClass H (compatible_dirac H hx) (compatible_dirac H hxw))
            (leftClass H (compatible_dirac H hxw) (compatible_dirac H hw.symm)))))
      (Path.Homotopic.Quotient.trans (rightClass H (compatible_dirac H hx) (compatible_dirac H hxy))
        (leftClass H (compatible_dirac H hxy) (compatible_dirac H hy.symm))))
    (Path.Homotopic.Quotient.symm
      (Path.Homotopic.Quotient.trans (rightClass H (compatible_dirac H hv) (compatible_dirac H hvy))
        (leftClass H (compatible_dirac H hvy) (compatible_dirac H hy.symm)))) = _
  simp only [quotient_symm_trans, leftClass_symm, rightClass_symm,
    Path.Homotopic.Quotient.trans_assoc, leftClass_trans_assoc, rightClass_trans_assoc]
  rw [rectangle_classes_commute_assoc H (compatible_dirac H hvw) (compatible_dirac H hvy)
    (compatible_dirac H hxw) (compatible_dirac H hxy)]
  simp only [leftClass_trans_assoc, leftClass_self,
    Path.Homotopic.Quotient.refl_trans, rightClass_trans, rightClass_self]
  rfl

end

end AbelianTargets.SupportPair


