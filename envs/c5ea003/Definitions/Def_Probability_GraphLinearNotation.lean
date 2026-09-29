-- Prove2me | Definitions.Def_Probability_GraphLinearNotation
-- name    : Probability_GraphLinearNotation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:46.707645+00:00
-- url     : https://prove2.me/theorems/7d3b5059-a17c-4109-842c-957711939f61
-- title:
--   Aether Catalog definitions — Probability_GraphLinearNotation
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GraphLinearNotation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GraphLinearNotation.lean by skeleton subtraction
import Mathlib
/-
  Graph Linear Notation

  For finite simple graphs on `Fin n`, we formalize *graph linear notation* (`gln`)
  as the maximum binary adjacency code taken over all vertex relabelings
  (permutations of the vertex set), and prove that it is a complete invariant for
  graph isomorphism.

  Main results:
  * `adjCode_injective`     : the ordered adjacency-matrix bit code is injective.
  * `gln_attained`          : the maximum defining `gln` is attained by some relabeling.
  * `gln_iso_invariant`     : isomorphic graphs have equal `gln`.
  * `gln_complete`          : equal `gln` implies isomorphism.
  * `gln_eq_iff_iso`        : `gln G = gln H ↔ IsGraphIso G H`.
-/

open Finset

namespace GraphLinearNotation

variable {n : ℕ}

/-- Relabel a graph by a vertex permutation: `i` and `j` are adjacent in
`permuteGraph σ G` iff `σ i` and `σ j` are adjacent in `G`. -/
def permuteGraph (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) :=
  G.comap σ


/-- Explicit graph isomorphism: a vertex permutation matching adjacencies. -/
def IsGraphIso (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, G.Adj i j ↔ H.Adj (σ i) (σ j)

open Classical in
/-- The adjacency bit at position `(i, j)`. -/
noncomputable def adjBit (G : SimpleGraph (Fin n)) (i j : Fin n) : ℕ :=
  if G.Adj i j then 1 else 0

/-- The natural-number bit encoding of the ordered adjacency matrix. -/
noncomputable def adjCode (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, adjBit G i j * 2 ^ (i.val * n + j.val)





/-
A sum of distinct powers of two with `0/1` coefficients determines the coefficients:
if `∑ i, f i * 2 ^ e i = ∑ i, g i * 2 ^ e i` with `e` injective and `f i, g i ≤ 1`, then `f = g`.
-/


/-- The finite set of adjacency codes over all relabelings is nonempty. -/
lemma orbitCodes_nonempty (G : SimpleGraph (Fin n)) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).image
      (fun σ => adjCode (permuteGraph σ G))).Nonempty :=
  (Finset.univ_nonempty (α := Equiv.Perm (Fin n))).image _

/-- **Graph linear notation**: the maximum adjacency code over all vertex relabelings. -/
noncomputable def gln (G : SimpleGraph (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).image
    (fun σ => adjCode (permuteGraph σ G))).max' (orbitCodes_nonempty G)








end GraphLinearNotation


