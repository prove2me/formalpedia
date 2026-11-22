-- Prove2me | Definitions.Def_Kourovka_Schreier_KernelPresentation
-- name    : Kourovka_Schreier_KernelPresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:18:08.869057+00:00
-- url     : https://prove2.me/theorems/3a990f36-d86c-43ec-a731-f8076d95f178
-- title:
--   Kernel Presentation
-- statement:
--   Definitions and structural lemmas for Kernel Presentation, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/KernelPresentation.lean

import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_rewrite
import Theorems.Thm_Kourovka_Schreier_Transversal_lift_inv
import Theorems.Thm_Kourovka_Schreier_Transversal_lift_map
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_eq_one
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk


set_option autoImplicit true
noncomputable section
namespace Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
def relators (R : Set (FreeGroup X)) : Set (FreeGroup S.Edge) :=
  {w | ∃ t : S.vertices, ∃ r ∈ R, S.rewrite t.val r = w} ∪
    Set.range (fun t : S.vertices => S.rewrite 1 t.val)
abbrev Presentation (R : Set (FreeGroup X)) := PresentedGroup (S.relators R)
abbrev label (R : Set (FreeGroup X)) : S.Edge → S.Presentation R := PresentedGroup.of
def relatorSubgroup (R : Set (FreeGroup X)) : Subgroup L :=
  (Subgroup.normalClosure R).comap L.subtype
instance relatorSubgroup_normal (R : Set (FreeGroup X)) :
    (relatorSubgroup (L := L) R).Normal :=
  inferInstanceAs (((Subgroup.normalClosure R).comap L.subtype).Normal)
theorem lift_label (R : Set (FreeGroup X)) (p w : FreeGroup X) :
    S.lift (S.label R) p w = PresentedGroup.mk (S.relators R) (S.rewrite p w) :=
  (S.lift_map (PresentedGroup.mk (S.relators R)) FreeGroup.of p w).symm
theorem lift_section (R : Set (FreeGroup X)) (t : S.vertices) :
    S.lift (S.label R) 1 t.val = 1 := by
  rw [lift_label]
  exact PresentedGroup.one_of_mem (Or.inr ⟨t, rfl⟩)
theorem lift_relator (R : Set (FreeGroup X)) {r : FreeGroup X} (hr : r ∈ R)
    (p : FreeGroup X) : S.lift (S.label R) p r = 1 := by
  calc
    _ = S.lift (S.label R) (S.rep p) r :=
      S.lift_start_eq _ (S.rep_rep p).symm r
    _ = _ := S.lift_label R (S.rep p) r
    _ = 1 := PresentedGroup.one_of_mem (Or.inl ⟨⟨S.rep p, ⟨p, rfl⟩⟩, r, hr, rfl⟩)
theorem rep_mul_of_normalClosure (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) {w : FreeGroup X}
    (hw : w ∈ Subgroup.normalClosure R) (p : FreeGroup X) :
    S.rep (p * w) = S.rep p := by
  apply S.constantOnCosets
  exact hR (Subgroup.Normal.conj_mem inferInstance w hw p)
theorem lift_normalClosure (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) {w : FreeGroup X}
    (hw : w ∈ Subgroup.normalClosure R) : ∀ p, S.lift (S.label R) p w = 1 := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨r, hr, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hw
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    intro p
    rw [lift_mul, lift_mul, lift_relator S R hr, mul_one]
    have hstart : S.rep (p * (g * r)) = S.rep (p * g) := by
      rw [← mul_assoc]
      exact S.rep_mul_of_normalClosure R hR (Subgroup.subset_normalClosure hr) (p * g)
    rw [S.lift_start_eq (S.label R) hstart g⁻¹, lift_inv, mul_inv_cancel]
  | one => intro p; rfl
  | mul u v _ _ hu hv =>
    intro p
    rw [lift_mul, hu, hv, one_mul]
  | inv u _ hu =>
    intro p
    have h := S.lift_mul (S.label R) p u⁻¹ u
    rw [inv_mul_cancel, lift_one, hu, mul_one] at h
    exact h.symm
theorem evaluate_relator (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) {w : FreeGroup S.Edge} (hw : w ∈ S.relators R) :
    (S.evaluate w).val ∈ Subgroup.normalClosure R := by
  rcases hw with ⟨t, r, hr, rfl⟩ | ⟨t, rfl⟩
  · rw [evaluate_rewrite, S.rep_vertex,
      S.rep_mul_of_normalClosure R hR (Subgroup.subset_normalClosure hr), S.rep_vertex]
    exact Subgroup.Normal.conj_mem inferInstance r (Subgroup.subset_normalClosure hr) t.val
  · rw [evaluate_rewrite, S.rep_one, one_mul, S.rep_vertex, mul_inv_cancel]
    exact Subgroup.one_mem _
def quotientMap (R : Set (FreeGroup X)) :
    FreeGroup S.Edge →* L ⧸ relatorSubgroup (L := L) R :=
  (QuotientGroup.mk' (relatorSubgroup (L := L) R)).comp S.evaluate
theorem quotientMap_relator (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) {w : FreeGroup S.Edge} (hw : w ∈ S.relators R) :
    S.quotientMap R w = 1 := by
  change QuotientGroup.mk (S.evaluate w) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (S.evaluate_relator R hR hw)
def forward (R : Set (FreeGroup X)) (hR : Subgroup.normalClosure R ≤ L) :
    S.Presentation R →* L ⧸ relatorSubgroup (L := L) R :=
  QuotientGroup.lift (Subgroup.normalClosure (S.relators R)) (S.quotientMap R)
    (fun _w hw => Subgroup.normalClosure_le_normal
      (N := (S.quotientMap R).ker) (fun _r hr => S.quotientMap_relator R hR hr) hw)
def backward (R : Set (FreeGroup X)) (hR : Subgroup.normalClosure R ≤ L) :
    L ⧸ relatorSubgroup (L := L) R →* S.Presentation R :=
  QuotientGroup.lift (relatorSubgroup (L := L) R) (S.subgroupLift (S.label R))
    (fun _w hw => S.lift_normalClosure R hR hw 1)
@[simp] theorem forward_mk (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (w : FreeGroup S.Edge) :
    S.forward R hR (PresentedGroup.mk (S.relators R) w) =
      QuotientGroup.mk' (relatorSubgroup (L := L) R) (S.evaluate w) := rfl
@[simp] theorem backward_mk (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (u : L) :
    S.backward R hR (QuotientGroup.mk' (relatorSubgroup (L := L) R) u) =
      S.lift (S.label R) 1 u.val := rfl
theorem lift_edgeValue_label (R : Set (FreeGroup X)) (z : S.Edge) :
    S.lift (S.label R) 1 (S.edgeValue z) = S.label R z := by
  let endpoint := S.rep (z.1.val * FreeGroup.of z.2)
  have hreturn : S.lift (S.label R) (z.1.val * FreeGroup.of z.2) endpoint⁻¹ = 1 := by
    calc
      _ = S.lift (S.label R) endpoint endpoint⁻¹ :=
        S.lift_start_eq _ (S.rep_rep _).symm _
      _ = (S.lift (S.label R) 1 endpoint)⁻¹ := by
        simpa only [one_mul] using S.lift_inv (S.label R) 1 endpoint
      _ = 1 := by rw [S.lift_section R ⟨endpoint, ⟨_, rfl⟩⟩, inv_one]
  change S.lift (S.label R) 1 ((z.1.val * FreeGroup.of z.2) * endpoint⁻¹) = _
  rw [lift_mul, lift_mul, S.lift_section R z.1, one_mul, one_mul, lift_of,
    S.edge_vertex, one_mul, hreturn, mul_one]
theorem backward_forward (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (u : S.Presentation R) :
    S.backward R hR (S.forward R hR u) = u := by
  have h : (S.backward R hR).comp (S.forward R hR) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro z
    change S.backward R hR (S.forward R hR
      (PresentedGroup.mk (S.relators R) (FreeGroup.of z))) = S.label R z
    rw [forward_mk, backward_mk, evaluate_of]
    exact S.lift_edgeValue_label R z
  exact DFunLike.congr_fun h u
theorem forward_backward (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (u : L ⧸ relatorSubgroup (L := L) R) :
    S.forward R hR (S.backward R hR u) = u := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (relatorSubgroup (L := L) R) u
  rw [backward_mk, lift_label, forward_mk]
  congr 1
  apply Subtype.ext
  rw [evaluate_rewrite, S.rep_one, one_mul, S.rep_eq_one v.property]
  simp
def presentationEquiv (R : Set (FreeGroup X)) (hR : Subgroup.normalClosure R ≤ L) :
    S.Presentation R ≃* L ⧸ relatorSubgroup (L := L) R where
  toFun := S.forward R hR
  invFun := S.backward R hR
  left_inv := S.backward_forward R hR
  right_inv := S.forward_backward R hR
  map_mul' := (S.forward R hR).map_mul
end Kourovka.Schreier.Transversal


