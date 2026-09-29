-- Prove2me | solution 1 for FundamentalGroupCompleteInvariant.homotopyEquiv_bijective_of_totallyDisconnected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:00:18.225797+00:00
-- url     : https://prove2.me/submissions/a07bfc4d-cb23-4585-92e7-d313ec9526b5

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


/-- A homotopy between maps into a totally disconnected space forces the maps
to be equal. -/
theorem homotopic_eq_of_totallyDisconnected [TotallyDisconnectedSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) : f = g := by
  obtain ⟨H⟩ := h
  ext x
  have hx : H (0, x) = H (1, x) :=
    TotallyDisconnectedSpace.eq_of_continuous (fun t : Set.Icc (0 : ℝ) 1 => H (t, x))
      (by fun_prop) 0 1
  simpa using hx








open FundamentalGroupCompleteInvariant in
theorem solution    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
    (e : X ≃ₕ Y) : Function.Bijective e := by
  -- left_inv and right_inv are homotopies
  have h1 : ⇑e.toFun ∘ ⇑e.invFun = ⇑(ContinuousMap.id Y) := by
    have := homotopic_eq_of_totallyDisconnected e.right_inv
    ext y
    exact ContinuousMap.ext_iff.mp this y
  have h2 : ⇑e.invFun ∘ ⇑e.toFun = ⇑(ContinuousMap.id X) := by
    have := homotopic_eq_of_totallyDisconnected e.left_inv
    ext x
    exact ContinuousMap.ext_iff.mp this x
  -- e.toFun is bijective since it has a two-sided inverse
  refine ⟨?_, ?_⟩
  · -- injective
    intro a b hab
    have ha : a = e.invFun (e.toFun a) := (congrFun h2 a).symm
    have hb : b = e.invFun (e.toFun b) := (congrFun h2 b).symm
    rw [ha, hb, hab]
  · -- surjective
    intro y
    use e.invFun y
    specialize h1
    replace h1 : e.toFun (e.invFun y) = y := by
      simpa using congrFun h1 y
    exact h1
