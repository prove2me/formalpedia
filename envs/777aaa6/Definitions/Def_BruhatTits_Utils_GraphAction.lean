-- Prove2me | Definitions.Def_BruhatTits_Utils_GraphAction
-- name    : BruhatTits_Utils_GraphAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:40:27.360439+00:00
-- url     : https://prove2.me/theorems/70a2ff57-f3fe-4a97-82e2-c1be54b33cbf
-- title:
--   Graph Action
-- statement:
--   Definitions and structural lemmas for Graph Action, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GraphAction.lean

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
set_option autoImplicit false
variable {V : Type*}
open SimpleGraph
section Action
class GraphAction (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) where
  smul_adj_smul (g : G) (x y : V) (h : X.Adj x y) : X.Adj (g • x) (g • y)
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]
namespace GraphAction
@[simp]
lemma adj_iff (g : G) (x y : V) : X.Adj (g • x) (g • y) ↔ X.Adj x y := by
  constructor
  · intro h
    simpa using smul_adj_smul g⁻¹ (g • x) (g • y) h
  · exact smul_adj_smul g x y
instance : SMul G (Sym2 V) where
  smul g := Sym2.map (fun x ↦ g • x)
@[simp]
lemma smul_sym2 (g : G) (x y : V) : g • s(x, y) = s(g • x, g • y) :=
  rfl
instance : MulAction G (Sym2 V) where
  one_smul x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp
  mul_smul g h x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp [mul_smul]
instance : SMul G X.edgeSet where
  smul g e := ⟨g • e.val, by
    have := e.property
    revert this
    generalize e.val = t
    refine Sym2.inductionOn t ?_
    intro x y
    simp⟩
@[simp]
lemma smul_edgeSet_coe (g : G) (e : X.edgeSet) : (g • e).val = g • e.val := rfl
instance : MulAction G X.edgeSet where
  one_smul x := by
    ext : 1
    simp
  mul_smul g x y := by
    ext : 1
    simp [mul_smul]
variable {G} {X}
lemma smul_mem_smul_of (g : G) (e : Sym2 V) (x : V) (h : x ∈ e) :
    g • x ∈ g • e := by
  revert h
  refine Sym2.inductionOn e ?_
  intro a b h
  simpa using h
@[simp]
lemma smul_mem_smul_iff (g : G) (e : Sym2 V) (x : V) :
    g • x ∈ g • e ↔ x ∈ e := by
  constructor
  · intro h
    simpa using smul_mem_smul_of g⁻¹ (g • e) (g • x) h
  · exact smul_mem_smul_of g e x
instance [MulAction.IsPretransitive G (Sym2 V)] : MulAction.IsPretransitive G X.edgeSet where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) x.val y.val
    use g
    ext : 1
    simpa
end GraphAction


