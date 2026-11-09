-- Prove2me | solution 1 for Couret.STROBO2TORS.tripleSupportsProfile_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:48.129915+00:00
-- url     : https://prove2.me/submissions/b0a044b3-05d2-4c5e-836b-482d7ab25330

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





































/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/

/-- Pairs of independent choices inside and outside the two-torsion set. -/
private def profilePairs (j : ℕ) : Finset (Finset G × Finset G) :=
  ((twoTorsion : Finset G).powersetCard j).product
    (((Finset.univ : Finset G) \ twoTorsion).powersetCard (3 - j))

/-- The part in H of a disjointly chosen union is its first component. -/
private theorem union_inter_twoTorsion_eq_left
    (A B : Finset G)
    (hA : A ⊆ (twoTorsion : Finset G))
    (hB : B ⊆ ((Finset.univ : Finset G) \ twoTorsion)) :
    (A ∪ B) ∩ (twoTorsion : Finset G) = A := by
  ext x
  constructor
  · intro hx
    rcases (Finset.mem_union.mp (Finset.mem_inter.mp hx).1) with ha | hb
    · exact ha
    · have hnot : x ∉ (twoTorsion : Finset G) :=
        (Finset.mem_sdiff.mp (hB hb)).2
      exact (hnot (Finset.mem_inter.mp hx).2).elim
  · intro ha
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union.mpr (Or.inl ha), hA ha⟩

/-- The part outside H of a disjointly chosen union is its second component. -/
private theorem union_sdiff_twoTorsion_eq_right
    (A B : Finset G)
    (hA : A ⊆ (twoTorsion : Finset G))
    (hB : B ⊆ ((Finset.univ : Finset G) \ twoTorsion)) :
    (A ∪ B) \ (twoTorsion : Finset G) = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨hu, hnot⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp hu with ha | hb
    · exact (hnot (hA ha)).elim
    · exact hb
  · intro hb
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inr hb),
        (Finset.mem_sdiff.mp (hB hb)).2⟩

/-- All fixed-j triples are precisely the unions of two complementary
choices, including the degenerate cases. -/
private theorem profilePairs_image_eq (j : ℕ) (hj : j ≤ 3) :
    (profilePairs (G := G) j).image (fun p => p.1 ∪ p.2) =
      tripleSupportsProfile (G := G) j := by
  ext S
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨haSub, haCard⟩ := Finset.mem_powersetCard.mp hpa
    obtain ⟨hbSub, hbCard⟩ := Finset.mem_powersetCard.mp hpb
    have hdis : Disjoint p.1 p.2 := by
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      have hnot : x ∉ (twoTorsion : Finset G) :=
        (Finset.mem_sdiff.mp (hbSub hxb)).2
      exact hnot (haSub hxa)
    have hint := union_inter_twoTorsion_eq_left p.1 p.2 haSub hbSub
    have hcard : (p.1 ∪ p.2).card = 3 := by
      rw [Finset.card_union_of_disjoint hdis, haCard, hbCard]
      omega
    exact (mem_tripleSupportsProfile (G := G) _ j).mpr
      ⟨hcard, by rw [hint, haCard]⟩
  · intro hS
    obtain ⟨hS3, hSJ⟩ := (mem_tripleSupportsProfile (G := G) S j).mp hS
    let A := S ∩ (twoTorsion : Finset G)
    let B := S \ (twoTorsion : Finset G)
    have hBCard : B.card = 3 - j := by
      have hc := Finset.card_sdiff_add_card_inter S (twoTorsion : Finset G)
      dsimp [A, B] at *
      omega
    have haSub : A ⊆ (twoTorsion : Finset G) :=
      Finset.inter_subset_right
    have hbSub : B ⊆ ((Finset.univ : Finset G) \ twoTorsion) := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hpair : (A, B) ∈ profilePairs (G := G) j := by
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_powersetCard.mpr ⟨haSub, hSJ⟩,
        Finset.mem_powersetCard.mpr ⟨hbSub, hBCard⟩⟩
    have hunion : A ∪ B = S := by
      ext x
      simp only [A, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    exact Finset.mem_image.mpr ⟨(A, B), hpair, hunion⟩

/-- Recover both choice components from their union. -/
private theorem profilePairs_union_injective (j : ℕ) :
    Set.InjOn (fun p : Finset G × Finset G => p.1 ∪ p.2)
      (profilePairs (G := G) j) := by
  intro p hp q hq heq
  rcases p with ⟨A, B⟩
  rcases q with ⟨C, D⟩
  change A ∪ B = C ∪ D at heq
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  obtain ⟨hc, hd⟩ := Finset.mem_product.mp hq
  have haSub := (Finset.mem_powersetCard.mp ha).1
  have hbSub := (Finset.mem_powersetCard.mp hb).1
  have hcSub := (Finset.mem_powersetCard.mp hc).1
  have hdSub := (Finset.mem_powersetCard.mp hd).1
  have hAC : A = C := by
    calc
      A = (A ∪ B) ∩ (twoTorsion : Finset G) :=
        (union_inter_twoTorsion_eq_left A B haSub hbSub).symm
      _ = (C ∪ D) ∩ (twoTorsion : Finset G) := by rw [heq]
      _ = C := union_inter_twoTorsion_eq_left C D hcSub hdSub
  have hBD : B = D := by
    calc
      B = (A ∪ B) \ (twoTorsion : Finset G) :=
        (union_sdiff_twoTorsion_eq_right A B haSub hbSub).symm
      _ = (C ∪ D) \ (twoTorsion : Finset G) := by rw [heq]
      _ = D := union_sdiff_twoTorsion_eq_right C D hcSub hdSub
  exact Prod.ext hAC hBD

/-- Exact binomial count of three-element supports with exactly j points
in G[2]. No assumption on the 2-rank or the existence of exceptions. -/
theorem p2m_local_tripleSupportsProfile_card (j : ℕ) (hj : j ≤ 3) :
    (tripleSupportsProfile (G := G) j).card =
      (twoTorsion : Finset G).card.choose j *
      ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) := by
  have hcount : (profilePairs (G := G) j).card =
      (twoTorsion : Finset G).card.choose j *
      ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) := by
    unfold profilePairs
    rw [Finset.product_eq_sprod, Finset.card_product]
    rw [Finset.card_powersetCard, Finset.card_powersetCard]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (twoTorsion : Finset G))]
    simp
  calc
    (tripleSupportsProfile (G := G) j).card =
        ((profilePairs (G := G) j).image (fun p => p.1 ∪ p.2)).card := by
          rw [profilePairs_image_eq j hj]
    _ = (profilePairs (G := G) j).card := by
          apply Finset.card_image_iff.mpr
          intro p hp q hq h
          exact profilePairs_union_injective j hp hq h
    _ = _ := hcount

end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j : Nat),
  @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.tripleSupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (Nat.choose (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) j)
        (Nat.choose
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))) := @_root_.Couret.STROBO2TORS.p2m_local_tripleSupportsProfile_card

