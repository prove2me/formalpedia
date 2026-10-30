-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.Polya.Weighted.weighted_polya
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:54:22.15428+00:00
-- url     : https://prove2.me/submissions/981cf7d1-6f61-429a-98b5-9ddfbbf36121

import Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Enumeration
import Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Weighted
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Weighted Pólya enumeration

This file proves the weighted fixed-coloring sum behind the cycle-index theorem
and packages it as a weighted Burnside/Pólya formula.
-/

namespace AnalyticCombinatorics.Ch1.Polya.Weighted

open scoped BigOperators

attribute [local instance] arrowAction

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Weighted.orbitRelDecidableRel

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Weighted.subtypeFintypeClassical

section General

variable {G D C R : Type*} [Group G] [MulAction G D] [Fintype D] [DecidableEq D]
  [Fintype C] [CommRing R]

omit [DecidableEq D] in
private theorem orbit_fiber_card (g : G)
    (σ : MulAction.orbitRel.Quotient (Subgroup.zpowers g) D) :
    (Finset.univ.filter fun d : D => (Quotient.mk'' d :
        MulAction.orbitRel.Quotient (Subgroup.zpowers g) D) = σ).card =
      Fintype.card σ.orbit := by
  classical
  exact
    (Fintype.card_of_finset'
      (Finset.univ.filter fun d : D => (Quotient.mk'' d :
          MulAction.orbitRel.Quotient (Subgroup.zpowers g) D) = σ)
      (p := σ.orbit)
      (by
        intro d
        simp [MulAction.orbitRel.Quotient.mem_orbit])).symm

omit [DecidableEq D] [Fintype C] in
private theorem orbit_color_prod (w : C → R) (g : G)
    (F : MulAction.orbitRel.Quotient (Subgroup.zpowers g) D → C) :
    (∏ d : D, w (F (Quotient.mk'' d))) =
      ∏ σ : MulAction.orbitRel.Quotient (Subgroup.zpowers g) D,
        w (F σ) ^ Fintype.card σ.orbit := by
  classical
  let Ω := MulAction.orbitRel.Quotient (Subgroup.zpowers g) D
  calc
    (∏ d : D, w (F (Quotient.mk'' d))) =
        ∏ σ : Ω, ∏ d ∈ (Finset.univ : Finset D) with
            (Quotient.mk'' d : Ω) = σ, w (F σ) := by
      simpa [Ω] using
        (Finset.prod_fiberwise' (s := (Finset.univ : Finset D))
          (g := fun d : D => (Quotient.mk'' d : Ω))
          (f := fun σ : Ω => w (F σ))).symm
    _ = ∏ σ : Ω, w (F σ) ^ Fintype.card σ.orbit := by
      refine Finset.prod_congr rfl ?_
      intro σ _
      rw [Finset.prod_const, orbit_fiber_card (G := G) (D := D) (g := g) σ]

/-- Weighted fixed-coloring sum for a single group element. -/
theorem sum_weight_fixedBy (w : C → R) (g : G) :
    (∑ f : {f : D → C // g • f = f}, coloringWeight w f.1) =
      ∏ σ : MulAction.orbitRel.Quotient (Subgroup.zpowers g) D,
        ∑ c : C, w c ^ Fintype.card σ.orbit := by
  classical
  let Ω := MulAction.orbitRel.Quotient (Subgroup.zpowers g) D
  calc
    (∑ f : {f : D → C // g • f = f}, coloringWeight w f.1) =
        ∑ F : Ω → C, ∏ d : D, w (F (Quotient.mk'' d)) := by
      refine Fintype.sum_equiv
        (fixedColoringEquiv (G := G) (D := D) (C := C) g) _ _ ?_
      intro f
      simp [coloringWeight, fixedColoringEquiv]
    _ = ∑ F : Ω → C, ∏ σ : Ω, w (F σ) ^ Fintype.card σ.orbit := by
      refine Finset.sum_congr rfl ?_
      intro F _
      exact orbit_color_prod (G := G) (D := D) (w := w) g F
    _ = ∏ σ : Ω, ∑ c : C, w c ^ Fintype.card σ.orbit := by
      simpa [Ω] using
        (Fintype.prod_sum (ι := Ω) (κ := fun _ => C) (R := R)
          (f := fun σ c => w c ^ Fintype.card σ.orbit)).symm

private theorem orbit_sum_stabilizer_weight_of_quotient {X : Type*} [MulAction G X] [Fintype X]
    [Fintype G] (W : X → R) (Wbar : MulAction.orbitRel.Quotient G X → R)
    (hWbar : ∀ x : X, Wbar (Quotient.mk'' x) = W x)
    (O : MulAction.orbitRel.Quotient G X) :
    (∑ x : O.orbit,
        ∑ _h : MulAction.stabilizer G (x : X), W (x : X)) =
      (Fintype.card G : R) * Wbar O := by
  classical
  have horbitCard :
      Fintype.card O.orbit * Fintype.card (MulAction.stabilizer G (O.out : X)) =
        Fintype.card G := by
    have hcongr :
        Fintype.card O.orbit = Fintype.card (MulAction.orbit G (O.out : X)) :=
      Fintype.card_congr
        (Equiv.setCongr (MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq'))
    rw [hcongr]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G (O.out : X)
  calc
    (∑ x : O.orbit,
        ∑ _h : MulAction.stabilizer G (x : X), W (x : X)) =
        ∑ _x : O.orbit,
          (Fintype.card (MulAction.stabilizer G (O.out : X)) : R) *
            Wbar O := by
      refine Finset.sum_congr rfl ?_
      intro x _
      have hxq :
          (Quotient.mk'' (x : X) : MulAction.orbitRel.Quotient G X) = O :=
        (MulAction.orbitRel.Quotient.mem_orbit (a := (x : X)) (x := O)).mp x.2
      have hxw :
          W (x : X) = Wbar O := by
        rw [← hWbar (x : X), hxq]
      have hxrel : MulAction.orbitRel G X (x : X) (O.out : X) := by
        rw [MulAction.orbitRel_apply]
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
        exact x.2
      have hstab :
          Fintype.card (MulAction.stabilizer G (x : X)) =
            Fintype.card (MulAction.stabilizer G (O.out : X)) :=
        Fintype.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hxrel).toEquiv
      calc
        (∑ _h : MulAction.stabilizer G (x : X), W (x : X)) =
            ∑ _h : MulAction.stabilizer G (x : X),
              Wbar O := by
          exact Finset.sum_congr rfl fun _ _ => hxw
        _ =
            (Fintype.card (MulAction.stabilizer G (x : X)) : R) *
              Wbar O := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ =
            (Fintype.card (MulAction.stabilizer G (O.out : X)) : R) *
              Wbar O := by
          rw [hstab]
    _ =
        (Fintype.card O.orbit : R) *
          ((Fintype.card (MulAction.stabilizer G (O.out : X)) : R) *
            Wbar O) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card G : R) * Wbar O := by
      rw [← mul_assoc, ← Nat.cast_mul, horbitCard]

private theorem weighted_burnside_of_quotient {X : Type*} [MulAction G X] [Fintype X]
    [Fintype G] (W : X → R) (Wbar : MulAction.orbitRel.Quotient G X → R)
    (hWbar : ∀ x : X, Wbar (Quotient.mk'' x) = W x) :
    (Fintype.card G : R) *
        (∑ O : MulAction.orbitRel.Quotient G X, Wbar O) =
      ∑ g : G, ∑ x : MulAction.fixedBy X g, W x.1 := by
  classical
  let Ω := MulAction.orbitRel.Quotient G X
  calc
    (Fintype.card G : R) *
        (∑ O : Ω, Wbar O) =
        ∑ O : Ω, (Fintype.card G : R) * Wbar O := by
      rw [Finset.mul_sum]
    _ = ∑ O : Ω, ∑ x : O.orbit,
        ∑ _h : MulAction.stabilizer G (x : X), W (x : X) := by
      refine Finset.sum_congr rfl ?_
      intro O _
      exact (orbit_sum_stabilizer_weight_of_quotient
        (G := G) (X := X) (R := R) W Wbar hWbar O).symm
    _ = ∑ y : Sigma fun O : Ω => O.orbit,
        ∑ _h : MulAction.stabilizer G (y.2 : X), W (y.2 : X) := by
      exact (Fintype.sum_sigma' fun (O : Ω) (x : O.orbit) =>
        ∑ _h : MulAction.stabilizer G (x : X), W (x : X)).symm
    _ = ∑ x : X, ∑ _h : MulAction.stabilizer G x, W x := by
      refine (Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits' G X) _ _ ?_).symm
      intro x
      rfl
    _ = ∑ p : Sigma fun x : X => MulAction.stabilizer G x, W p.1 := by
      exact (Fintype.sum_sigma' fun x (_h : MulAction.stabilizer G x) =>
        W x).symm
    _ = ∑ p : Sigma fun g : G => MulAction.fixedBy X g, W p.2.1 := by
      refine (Fintype.sum_equiv (sigmaFixedByEquivSigmaStabilizer G X) _ _ ?_).symm
      intro p
      rfl
    _ = ∑ g : G, ∑ x : MulAction.fixedBy X g, W x.1 := by
      exact Fintype.sum_sigma' fun g (x : MulAction.fixedBy X g) => W x.1

/-- Weighted Burnside's lemma for coloring weights. -/
theorem weighted_burnside [Fintype G] :
    (Fintype.card G : R) *
        (∑ O : MulAction.orbitRel.Quotient G (D → C), orbitWeight (G := G) (D := D) w O) =
      ∑ g : G, ∑ f : MulAction.fixedBy (D → C) g, coloringWeight w f.1 := by
  classical
  exact weighted_burnside_of_quotient
    (G := G) (X := D → C) (R := R)
    (coloringWeight w) (orbitWeight (G := G) (D := D) w) (by intro f; rfl)

end General
end AnalyticCombinatorics.Ch1.Polya.Weighted

attribute [local instance] _root_.arrowAction
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Weighted.orbitRelDecidableRel
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Weighted.subtypeFintypeClassical
open AnalyticCombinatorics AnalyticCombinatorics.Ch1 AnalyticCombinatorics.Ch1.Polya AnalyticCombinatorics.Ch1.Polya.Weighted
open scoped BigOperators
variable {G D C R : Type*} [Group G] [MulAction G D] [Fintype D] [DecidableEq D]
  [Fintype C] [CommRing R]
theorem solution [Fintype G] :
    (Fintype.card G : R) *
        (∑ O : MulAction.orbitRel.Quotient G (D → C), orbitWeight (G := G) (D := D) w O) =
      ∑ g : G,
        ∏ σ : MulAction.orbitRel.Quotient (Subgroup.zpowers g) D,
          ∑ c : C, w c ^ Fintype.card σ.orbit := by
  classical
  rw [weighted_burnside (G := G) (D := D) (C := C) (R := R) (w := w)]
  refine Finset.sum_congr rfl ?_
  intro g _
  exact sum_weight_fixedBy (G := G) (D := D) (C := C) (R := R) w g
