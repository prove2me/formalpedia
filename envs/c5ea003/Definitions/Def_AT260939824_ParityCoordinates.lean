-- Prove2me | Definitions.Def_AT260939824_ParityCoordinates
-- name    : AT260939824_ParityCoordinates
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:41:55.850198+00:00
-- url     : https://prove2.me/theorems/1de0619b-007c-4f1f-a43b-d0cbde254676
-- title:
--   A unimodular parity coordinate change
-- statement:
--   For $d\ge1$, the first axis is chosen in the integer lattice $\mathbb Z^d$. A shear replaces the first coordinate by the sum of all coordinates and keeps the transverse coordinates; an explicit inverse subtracts their sum. These mutually inverse additive maps define a lattice automorphism. Every original generator has first sheared coordinate one, which makes its parity action uniform.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ParityCoordinates.lean, selected declaration lines 17, 19-20, 22-24, 26-31, 33-44, 46-64, 66-78, 80-81; SHA-256 82a0293d506c6ea5ab4468b02ff1f9fecb2a791a0d725cc1f7c75a22a2c8eb1c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# The unimodular parity coordinate change in Proposition 6.1

The new first coordinate is the sum of the original coordinates. Hence
every original generator has first coordinate one, and each of the
remaining generators changes only one transverse coordinate as well.
-/

namespace AbelianTargets

open scoped BigOperators

def firstAxis {d : ℕ} (hd : 1 ≤ d) : Fin d := ⟨0, by omega⟩

def shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) : Lattice d :=
  fun i => if i = firstAxis hd then ∑ j, g j else g i

def unshearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) : Lattice d :=
  fun i => if i = firstAxis hd then
    g (firstAxis hd) - ∑ j ∈ Finset.univ.erase (firstAxis hd), g j else g i

theorem sum_erase_shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    (∑ j ∈ Finset.univ.erase (firstAxis hd), shearCoordinates hd g j) =
      ∑ j ∈ Finset.univ.erase (firstAxis hd), g j := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [shearCoordinates, if_neg (Finset.mem_erase.mp hj).1]

theorem unshear_shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    unshearCoordinates hd (shearCoordinates hd g) = g := by
  funext i
  by_cases hi : i = firstAxis hd
  · subst i
    change (∑ j, g j) - (∑ j ∈ Finset.univ.erase (firstAxis hd),
      shearCoordinates hd g j) = g (firstAxis hd)
    rw [sum_erase_shearCoordinates]
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) g
      (Finset.mem_univ (firstAxis hd))
    omega
  · simp [unshearCoordinates, shearCoordinates, hi]

theorem shear_unshearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    shearCoordinates hd (unshearCoordinates hd g) = g := by
  funext i
  by_cases hi : i = firstAxis hd
  · subst i
    change (∑ j, unshearCoordinates hd g j) = g (firstAxis hd)
    have hsum : (∑ j ∈ Finset.univ.erase (firstAxis hd), unshearCoordinates hd g j) =
        ∑ j ∈ Finset.univ.erase (firstAxis hd), g j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [unshearCoordinates, if_neg (Finset.mem_erase.mp hj).1]
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (unshearCoordinates hd g) (Finset.mem_univ (firstAxis hd))
    change (∑ j ∈ Finset.univ.erase (firstAxis hd), unshearCoordinates hd g j) +
      (g (firstAxis hd) - ∑ j ∈ Finset.univ.erase (firstAxis hd), g j) =
      ∑ j, unshearCoordinates hd g j at he
    rw [hsum] at he
    omega
  · simp [unshearCoordinates, shearCoordinates, hi]

/-- The literal integer-lattice automorphism corresponding to the
basis `e₁, e₂-e₁, …, e_d-e₁`. -/
def parityCoordinateEquiv {d : ℕ} (hd : 1 ≤ d) : Lattice d ≃+ Lattice d where
  toFun := shearCoordinates hd
  invFun := unshearCoordinates hd
  left_inv := unshear_shearCoordinates hd
  right_inv := shear_unshearCoordinates hd
  map_add' := by
    intro g h
    funext i
    by_cases hi : i = firstAxis hd
    · simp [shearCoordinates, hi, Finset.sum_add_distrib]
    · simp [shearCoordinates, hi]

@[simp] theorem shearCoordinates_first {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    shearCoordinates hd g (firstAxis hd) = ∑ i, g i := by simp [shearCoordinates]







end AbelianTargets


