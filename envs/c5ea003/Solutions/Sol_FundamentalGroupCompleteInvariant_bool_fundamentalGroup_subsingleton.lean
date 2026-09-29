-- Prove2me | solution 1 for FundamentalGroupCompleteInvariant.bool_fundamentalGroup_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:00:17.182504+00:00
-- url     : https://prove2.me/submissions/07999d6e-1cb0-45e3-aeec-dfc5160ec51f

-- Sol generated from Bridges/FundamentalGroupCompleteInvariant.lean
import Mathlib
import Definitions.Def_Bridges_FundamentalGroupCompleteInvariant
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
/-
# Fundamental groups classify connected homotopy 1-types

A connected groupoid is the algebraic model of a connected homotopy 1-type
(an Eilenberg--MacLane type `K(G,1)`).  This file proves that such a groupoid is
completely classified, up to equivalence, by the automorphism group of one
basepoint.  It also proves a topological counterexample showing why no analogous
classification holds for arbitrary spaces.
-/

open CategoryTheory
open scoped ContinuousMap

open FundamentalGroupCompleteInvariant

universe u v u' v'



variable {C : Type u} [Groupoid.{v} C] (c : C)











variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]










open FundamentalGroupCompleteInvariant in
theorem solution(b : Bool) :
    Subsingleton (FundamentalGroup Bool b) := by
  rw [FundamentalGroup]
  rw [End]
  -- Let X be the object in the fundamental groupoid with X.as = b
  set X : FundamentalGroupoid Bool := ⟨b⟩ with hX
  -- Hom type is a quotient of Path X.as X.as
  -- All paths in Bool are constant, so the quotient is trivial
  have heq : (X ⟶ X) = _root_.Quotient (Path.Homotopic.setoid X.as X.as) := rfl
  rw [heq]
  rw [Quotient.subsingleton_iff]
  -- Need to show that Path.Homotopic.setoid is trivial
  -- i.e., any two paths from b to b are homotopic
  ext p q
  -- Need to show Path.Homotopic p q (since ⊤ p q is always true)
  constructor
  · intro _; trivial
  · intro _
    -- Show that p = q (since any continuous map [0,1] → Bool is constant)
    have hpq : p = q := by
      -- Any continuous map [0,1] → Bool is constant
      -- So p and q are both constant at b
      ext t
      -- p t = p 0 since p is continuous and Bool is totally disconnected
      have hp_const : ∀ t, p t = p 0 := by
        intro t
        exact TotallyDisconnectedSpace.eq_of_continuous (fun s : Set.Icc (0:ℝ) 1 => p s) (by fun_prop) t 0
      have hq_const : ∀ t, q t = q 0 := by
        intro t
        exact TotallyDisconnectedSpace.eq_of_continuous (fun s : Set.Icc (0:ℝ) 1 => q s) (by fun_prop) t 0
      rw [hp_const, hq_const]
      -- p 0 = source of p = b and q 0 = source of q = b
      simp
    rw [hpq]
