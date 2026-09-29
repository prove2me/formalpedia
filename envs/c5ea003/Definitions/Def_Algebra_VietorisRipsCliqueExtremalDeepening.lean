-- Prove2me | Definitions.Def_Algebra_VietorisRipsCliqueExtremalDeepening
-- name    : Algebra_VietorisRipsCliqueExtremalDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:21:39.215152+00:00
-- url     : https://prove2.me/theorems/6cbae467-05d4-483e-b5e7-12a998e459c4
-- title:
--   Aether Catalog definitions — Algebra_VietorisRipsCliqueExtremalDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.VietorisRipsCliqueExtremalDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/VietorisRipsCliqueExtremalDeepening.lean by skeleton subtraction
import Mathlib

/-!
# Rigidity of the extremal Vietoris–Rips clique count

The elementary bound saying that a graph on `n` vertices has at most `2^n` cliques
leaves open its equality case.  This file proves the sharp rigidity statement for every
finite vertex type: a graph has as many cliques as subsets if and only if it is complete.
It also derives strict monotonicity of clique-complex size when an edge is added, and a
metric consequence: a Vietoris–Rips complex has maximal size exactly when every pair is
within the scale.
-/

noncomputable section

open Classical Finset

namespace VRCliqueExtremalDeepening

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite clique complex of a graph on an arbitrary finite vertex type. -/
def cliqueFamily (H : SimpleGraph α) : Finset (Finset α) :=
  Finset.univ.powerset.filter fun S => H.IsClique (↑S : Set α)








/-- A symmetric dissimilarity gives a proximity graph at scale `r`. -/
def proximityGraph (D : α → α → ℝ) (r : ℝ) : SimpleGraph α where
  Adj i j := i ≠ j ∧ D i j ≤ r ∧ D j i ≤ r
  symm := by rintro i j ⟨hij, hijr, hjir⟩; exact ⟨hij.symm, hjir, hijr⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- The finite Vietoris–Rips complex of a dissimilarity on an arbitrary finite type. -/
def vrComplex (D : α → α → ℝ) (r : ℝ) : Finset (Finset α) :=
  Finset.univ.powerset.filter fun S => ∀ i ∈ S, ∀ j ∈ S, D i j ≤ r




end VRCliqueExtremalDeepening


