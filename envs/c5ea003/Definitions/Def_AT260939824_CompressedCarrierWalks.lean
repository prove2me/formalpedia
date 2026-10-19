-- Prove2me | Definitions.Def_AT260939824_CompressedCarrierWalks
-- name    : AT260939824_CompressedCarrierWalks
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:53:48.829145+00:00
-- url     : https://prove2.me/theorems/7552603a-e088-4a3d-9c11-41744a058b4c
-- title:
--   Bottom vertices in finite interval carriers
-- statement:
--   For nonnegative integers $K,R,n$ with $n\le R$, the designated bottom vertex is the carrier vertex
--
--   $$ v_n=(n,0),\qquad 0\le n\le R. $$
--
--   The definition includes its interval and height membership witness. This provides the fixed endpoint indexing used by compressed carrier walks and bottom-edge interpolation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CompressedCarrierWalks.lean, selected declaration lines 122-124; SHA-256 6ede68e0ab4a687cc4ae1c6307e09f6d6c395a3d118bb1b64736614152934373. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_IntervalCarriers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Actual logarithmically short walks in finite interval carriers

The recursive digit path is constructed in the literal skeleton graph.
All of its vertices stay in the horizontal interval between its endpoints
and below the digit height. Consequently it gives an actual walk in the
finite induced carrier, with the explicit logarithmic length bound.
-/

namespace AbelianTargets.IntervalCarriers

open SimpleGraph





def bottomVertex (K R n : ℕ) (hn : n ≤ R) :
    {v : Vertex // v ∈ carrierVertices K 0 R} :=
  ⟨((n : ℤ),0), mem_carrierVertices.mpr ⟨by positivity, by change (n : ℤ) ≤ R; exact_mod_cast hn, by omega⟩⟩



end AbelianTargets.IntervalCarriers


