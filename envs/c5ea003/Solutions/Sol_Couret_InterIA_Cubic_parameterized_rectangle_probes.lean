-- Prove2me | solution 1 for Couret.InterIA.Cubic.parameterized_rectangle_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:16.984558+00:00
-- url     : https://prove2.me/submissions/c0ca15de-9f55-42a1-9aa4-b3ec78428651

import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Theorems.Thm_Couret_InterIA_Cubic_rectangle_two_coordinates
import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Cubic





theorem p2m_local_parameterized_rectangle_probes {α ι : Type*}
    (q : α → ι → ℝ) (F : Set α) (g : Bool × Bool → α)
    (hg : Function.Injective g) (hmem : ∀ p, g p ∈ F)
    (hcover : ∀ A ∈ F, ∃ p, g p=A) (hinj : Set.InjOn q F)
    (H U V : ι → ℝ) (hrect : ∀ p, q (g p)=rectangle H U V p) :
    ∃ Q : Finset ι, Q.card≤2 ∧ Separates q F Q := by
  classical
  have hr : Function.Injective (rectangle H U V) := by
    intro p r he
    apply hg
    apply hinj (hmem p) (hmem r)
    exact (hrect p).trans (he.trans (hrect r).symm)
  obtain ⟨z,w,hi⟩ := rectangle_two_coordinates H U V hr
  refine ⟨{z,w},by by_cases he : z=w <;> simp [he],?_⟩
  intro A hA B hB he
  obtain ⟨p,rfl⟩ := hcover A hA
  obtain ⟨r,rfl⟩ := hcover B hB
  apply congrArg g
  apply hi
  apply Prod.ext
  · exact (congrFun (hrect p) z).symm.trans
      ((he z (by simp)).trans (congrFun (hrect r) z))
  · exact (congrFun (hrect p) w).symm.trans
      ((he w (by simp)).trans (congrFun (hrect r) w))

end Couret.InterIA.Cubic

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {α : Type p2m_u_0} {ι : Type p2m_u_1} (q : α → ι → Real) (F : Set.{p2m_u_0} α) (g : Prod.{0, 0} Bool Bool → α),
  @Function.Injective.{1, p2m_u_0 + 1} (Prod.{0, 0} Bool Bool) α g →
    (∀ (p : Prod.{0, 0} Bool Bool),
        @Membership.mem.{p2m_u_0, p2m_u_0} α (Set.{p2m_u_0} α) (@Set.instMembership.{p2m_u_0} α) F (g p)) →
      (∀ (A : α),
          @Membership.mem.{p2m_u_0, p2m_u_0} α (Set.{p2m_u_0} α) (@Set.instMembership.{p2m_u_0} α) F A →
            @Exists.{1} (Prod.{0, 0} Bool Bool) fun p => @Eq.{p2m_u_0 + 1} α (g p) A) →
        @Set.InjOn.{p2m_u_0, p2m_u_1} α (ι → Real) q F →
          ∀ (H U V : ι → Real),
            (∀ (p : Prod.{0, 0} Bool Bool),
                @Eq.{p2m_u_1 + 1} (ι → Real) (q (g p)) (@Couret.InterIA.Cubic.rectangle.{p2m_u_1} ι H U V p)) →
              @Exists.{p2m_u_1 + 1} (Finset.{p2m_u_1} ι) fun Q =>
                And
                  (@LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_1} ι Q)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Couret.InterIA.Cubic.Separates.{p2m_u_0, p2m_u_1} α ι q F Q) := @_root_.Couret.InterIA.Cubic.p2m_local_parameterized_rectangle_probes

