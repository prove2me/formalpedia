-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Weighted
-- name    : AnalyticCombinatorics_Ch1_Polya_Weighted
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:50:00.502724+00:00
-- url     : https://prove2.me/theorems/1d179f92-2514-4e5c-84f7-42c0ff4a7258
-- title:
--   Multiplicative weights of coloring orbits
-- statement:
--   For a finite position set $D$ acted on by a group $G$, and color weights $w:C\to R$ in a commutative ring, a coloring $f:D\to C$ has weight $\prod_{d\in D}w(f(d))$. This product is invariant under the induced group action, so it defines a weight on each coloring orbit. The foundation also constructs the bijection between pairs $(g,x)$ with $g\cdot x=x$ and pairs $(x,g)$ with $g$ in the stabilizer of $x$; this bijection applies to arbitrary group actions without a finiteness assumption. No positivity, division by the group size, or invertibility of color weights is required.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Polya/Weighted.lean
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable local instance orbitRelDecidableRel {H X : Type*} [Group H] [MulAction H X] :
    DecidableRel (MulAction.orbitRel H X).r :=
  Classical.decRel _

noncomputable local instance subtypeFintypeClassical {X : Type*} [Fintype X] (p : X → Prop) :
    Fintype {x // p x} :=
  @Subtype.fintype X p (Classical.decPred p) inferInstance

section General

variable {G D C R : Type*} [Group G] [MulAction G D] [Fintype D] [DecidableEq D]
  [Fintype C] [CommRing R]

/-- The multiplicative weight of a coloring. -/
def coloringWeight (w : C → R) (f : D → C) : R :=
  ∏ d : D, w (f d)

omit [DecidableEq D] [Fintype C] in
/-- The coloring weight is invariant under the arrow action on colorings. -/
theorem coloringWeight_smul (w : C → R) (g : G) (f : D → C) :
    coloringWeight w (g • f) = coloringWeight w f := by
  classical
  simpa [coloringWeight, arrowAction] using
    (Equiv.prod_comp (MulAction.toPerm (g⁻¹)) fun d : D => w (f d))

/-- The coloring weight descends to the quotient by the full group action. -/
noncomputable def orbitWeight (w : C → R) :
    MulAction.orbitRel.Quotient G (D → C) → R :=
  fun O =>
    Quotient.liftOn' O (fun f => coloringWeight w f) fun f f' h => by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
      rcases h with ⟨g, hg⟩
      rw [← hg]
      exact coloringWeight_smul (D := D) w g f'

omit [DecidableEq D] [Fintype C] in
@[simp]
theorem orbitWeight_mk (w : C → R) (f : D → C) :
    orbitWeight (G := G) (D := D) w
        (Quotient.mk'' f : MulAction.orbitRel.Quotient G (D → C)) =
      coloringWeight w f :=
  rfl

noncomputable def sigmaFixedByEquivSigmaStabilizer
    (G X : Type*) [Group G] [MulAction G X] :
    (Sigma fun g : G => MulAction.fixedBy X g) ≃
      Sigma fun x : X => MulAction.stabilizer G x where
  toFun p :=
    ⟨p.2.1, ⟨p.1, by
      change p.1 • (p.2.1 : X) = p.2.1
      exact p.2.2⟩⟩
  invFun p :=
    ⟨p.2.1, ⟨p.1, by
      change (p.2.1 : G) • p.1 = p.1
      exact p.2.2⟩⟩
  left_inv p := by
    cases p with
    | mk g f =>
      cases f
      rfl
  right_inv p := by
    cases p with
    | mk f g =>
      cases g
      rfl

end General

end AnalyticCombinatorics.Ch1.Polya.Weighted


