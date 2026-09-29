-- Prove2me | Definitions.Def_Applications_HamiltonianCompression_Defs
-- name    : Applications_HamiltonianCompression_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:48.355978+00:00
-- url     : https://prove2.me/theorems/ed7fcfac-b26d-453a-a764-997ea3f1c5fb
-- title:
--   Aether Catalog definitions — Applications_HamiltonianCompression_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.HamiltonianCompression.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/HamiltonianCompression/Defs.lean by skeleton subtraction
import Mathlib
/-
# Hamiltonian Compression Factor of Cubic Edge-Transitive Graphs

## Mission framing
A graph `Γ` has *Hamiltonian compression factor* `κ(Γ) ≥ k` when it admits a
`k`-symmetric Hamiltonian cycle: a Hamiltonian cycle `C` together with an
automorphism `g` of order `k` that acts on `C` as a rotation by `|V(Γ)|/k`
positions.  The research conjecture asserts that *every* Hamiltonian connected
cubic edge-transitive graph satisfies `κ(Γ) ≥ 2`.

This file sets up a self-contained, faithful formalization of `κ ≥ 2`
(a *2-symmetric Hamiltonian cycle*) and the cubic circulant family on which we
prove it.  The carrier of every graph is `ZMod n`, so that the "rotation by
`n/2`" automorphism is literally translation by the diameter element `n/2`.

The connection set `{±1, n/2}` produces the **Möbius–Kantor / Möbius ladder**
cubic circulant `ML(n)`.  Its smallest members are genuine *cubic
edge-transitive* graphs:
  * `ML(4) = K₄`         (complete graph on 4 vertices),
  * `ML(6) = K_{3,3}`    (complete bipartite, the 3-cube's bipartite double).
For every even `n ≥ 4` the graph `ML(n)` is `3`-regular (cubic) and vertex
transitive, and we prove it carries a 2-symmetric Hamiltonian cycle, giving an
infinite family of evidence for `κ ≥ 2`.
-/

open Equiv Finset

namespace HamiltonianCompression

/-- The *diameter element* `n/2 ∈ ZMod n`; translation by it is the candidate
order-2 rotation of a `2`-symmetric Hamiltonian cycle. -/
def diam (n : ℕ) : ZMod n := (↑(n / 2) : ZMod n)

/-- Möbius-ladder / cubic circulant adjacency on `ZMod n`, with connection set
`{+1, -1, n/2}`.  For even `n` this is a symmetric, irreflexive relation. -/
def MLAdj (n : ℕ) (a b : ZMod n) : Prop :=
  a - b = 1 ∨ a - b = -1 ∨ a - b = diam n

instance (n : ℕ) : DecidableRel (MLAdj n) := by
  intro a b; unfold MLAdj; infer_instance





end HamiltonianCompression


