-- Prove2me | Definitions.Def_Applications_Combinatorics_Ramsey
-- name    : Applications_Combinatorics_Ramsey
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:33.391659+00:00
-- url     : https://prove2.me/theorems/0ab6b849-d427-4a45-b46b-333c3db85a7f
-- title:
--   Aether Catalog definitions — Applications_Combinatorics_Ramsey
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Combinatorics.Ramsey`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Combinatorics/Ramsey.lean by skeleton subtraction
import Mathlib
/-
# Finite two‑colour Ramsey theory

This file develops the elementary theory of finite two‑colour Ramsey numbers,
culminating in the exact value `R(3,3) = 6` and the Erdős–Szekeres binomial
upper bound `R(s+1, t+1) ≤ C(s+t, s)`.

A *two‑colouring* of a complete graph is encoded by a single `SimpleGraph G`:
the edges of `G` are the **red** edges and the edges of its complement `Gᶜ`
are the **blue** edges.  A red clique is then a clique of `G` and a blue clique
is a clique of `Gᶜ`.

The central relation is the *arrow* relation `Arrows n s t`
(classically written `n → (s, t)`): every red/blue colouring of any vertex set
of size at least `n` contains a red `s`‑clique or a blue `t`‑clique.
-/


open scoped Classical
open SimpleGraph Finset

namespace RamseyTheory

/-! ## Core combinatorial objects -/


/-- `Arrows n s t` is the *arrow* relation `n → (s, t)`:
for every red/blue colouring `G` of a complete graph on a vertex set `W`
of size at least `n`, there is a **red** `s`‑clique (a clique of `G`) contained
in `W`, or a **blue** `t`‑clique (a clique of `Gᶜ`) contained in `W`.

Quantifying over an arbitrary vertex type together with a `Finset W` of vertices
bakes in monotonicity in the number of vertices and makes the Erdős–Szekeres
recursion easy to state, since the two recursive calls live on subsets of the
same vertex set. -/
def Arrows (n s t : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (W : Finset V), n ≤ W.card →
    (∃ S : Finset V, S ⊆ W ∧ G.IsNClique s S) ∨
    (∃ S : Finset V, S ⊆ W ∧ Gᶜ.IsNClique t S)

/-! ## Monotonicity -/


/-! ## The Erdős–Szekeres recursion -/






/-! ## The value `R(3,3) = 6` -/


/-- The pentagon (`5`‑cycle) `C₅`, used as the extremal colouring witnessing
`R(3,3) > 5`.  Adjacency is `a + 1 = b` or `b + 1 = a` (indices mod `5`). -/
def pentagon : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b => a + 1 = b)

instance : DecidableRel pentagon.Adj := by unfold pentagon; infer_instance





end RamseyTheory


