-- Prove2me | Definitions.Def_Combinatorics_Basic
-- name    : Combinatorics_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:28:23.355897+00:00
-- url     : https://prove2.me/theorems/17d4c156-2b4c-4e2f-b447-7d5958996617
-- title:
--   Aether Catalog definitions — Combinatorics_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Basic.lean by skeleton subtraction
import Mathlib
/-
# Divisors, the graph Laplacian, and chip-firing: basic theory

This file sets up the divisor theory of a finite graph (the combinatorial model of a
tropical curve / metric graph), following Baker–Norine.

Main definitions:
* `TropicalRR.Divisor V` : an element of `ℤ^V`;
* `TropicalRR.degD` : the degree of a divisor;
* `TropicalRR.lap G f` : the graph Laplacian applied to `f : V → ℤ`;
* `TropicalRR.LinEquiv G` : linear equivalence of divisors (`D' = D - lap f`);
* `TropicalRR.Effective`, `TropicalRR.Winnable` : effectivity and winnability of a divisor.

Main results:
* `TropicalRR.degD_lap` : the Laplacian image has degree `0`;
* `TropicalRR.LinEquiv.degD_eq` : linear equivalence preserves degree;
* `TropicalRR.const_of_lap_eq_zero` : on a connected graph the kernel of the
  Laplacian consists exactly of the constants;
* `TropicalRR.lap_indicator` : the set-firing formula.
-/

namespace TropicalRR

open Finset

variable {V : Type*} [Fintype V]

/-- A divisor on a graph with vertex set `V` is an integer-valued function on vertices. -/
abbrev Divisor (V : Type*) := V → ℤ

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree of a divisor. -/
def degD (D : Divisor V) : ℤ := ∑ v, D v

/-- The graph Laplacian applied to an integer function.  Subtracting `lap G f` from a
divisor is the result of firing `f v` chips from each vertex `v`. -/
def lap (f : V → ℤ) : Divisor V := fun v => ∑ w ∈ G.neighborFinset v, (f v - f w)










/-! ### Linear equivalence -/

/-- Two divisors are linearly equivalent when they differ by an element of the image of
the Laplacian, i.e. one is obtained from the other by a chip-firing move. -/
def LinEquiv (D D' : Divisor V) : Prop := ∃ f : V → ℤ, D' = D - lap G f







/-! ### Effectivity -/

/-- A divisor is effective when it is everywhere nonnegative. -/
def Effective (D : Divisor V) : Prop := ∀ v, 0 ≤ D v



/-- A divisor is *winnable* if it is linearly equivalent to an effective divisor;
this is the set `W` in the Baker–Norine dichotomy. -/
def Winnable (D : Divisor V) : Prop := ∃ D', LinEquiv G D D' ∧ Effective D'






/-! ### The kernel of the Laplacian -/



variable [DecidableEq V]

/-! ### Firing a set of vertices -/

/-- The indicator function of a finset, as an integer function. -/
def indic (S : Finset V) : V → ℤ := fun v => if v ∈ S then 1 else 0

/-- The number of edges from `v` leaving the set `S`. -/
def outdeg (S : Finset V) (v : V) : ℕ := ((G.neighborFinset v) \ S).card

/-- The number of edges from `v` into the set `S`. -/
def indeg (S : Finset V) (v : V) : ℕ := ((G.neighborFinset v) ∩ S).card




/-! ### The set where a function attains its maximum -/

/-- The set of vertices at which `f` attains its maximum. -/
def maxSet (f : V → ℤ) : Finset V := Finset.univ.filter (fun v => ∀ w, f w ≤ f v)









/-! ### Genus and the canonical divisor -/

/-- The genus (first Betti number) of a connected graph: `|E| - |V| + 1`. -/
def genus : ℤ := (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) + 1

/-- The canonical divisor `K = ∑ (deg v - 2) v`. -/
def canonical : Divisor V := fun v => (G.degree v : ℤ) - 2


end TropicalRR


