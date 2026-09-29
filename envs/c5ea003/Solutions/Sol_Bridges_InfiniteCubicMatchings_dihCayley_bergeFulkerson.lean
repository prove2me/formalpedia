-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.dihCayley_bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:42:36.394086+00:00
-- url     : https://prove2.me/submissions/47a6ad6f-4203-48cd-b7b7-dc05daa738dc

-- Sol generated from Bridges/InfiniteCubicMatchingsCayley.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Theorems.Thm_Bridges_InfiniteCubicMatchings_ProperThreeEdgeColoring_bergeFulkerson
import Theorems.Thm_Bridges_InfiniteCubicMatchings_cayley_properThreeEdgeColoring_of_involutions
/-
# Cayley graphs: infinite cubic Berge–Fulkerson graphs from finite quotients

A cubic Cayley graph `cayley S` of a group `Γ` (with `S` a three-element, inverse-closed
generating set of non-identity elements) is a covering of the Cayley graph of any quotient
`Γ →* Δ` on which the generators stay distinct and nontrivial (`isLocalIsoAt_cayley`).

Combining this with `BergeFulkerson.of_covering` gives a group-theoretic source of infinite
examples:

* `cayley_bergeFulkerson_of_quotient` — if the (possibly finite) quotient Cayley graph
  satisfies Berge–Fulkerson, so does the infinite one upstairs;
* `cayley_bergeFulkerson_of_finite_quotient` — assuming only the *finite* Berge–Fulkerson
  conjecture, every cubic Cayley graph of an infinite group with a suitable finite quotient
  satisfies Berge–Fulkerson;
* `ladderGroup_*` — a concrete instantiation with `Γ = ℤ × ℤ/2`, whose Cayley graph is the
  infinite ladder and whose finite quotients are the prisms.
-/

open Bridges.InfiniteCubicMatchings

universe u v


variable {Γ : Type u} [Group Γ] {Δ : Type v} [Group Δ]


variable (S : Set Γ) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hS1 : (1 : Γ) ∉ S)






/-- Berge–Fulkerson for cubic Cayley graphs on three involutions. -/
theorem cayley_bergeFulkerson_of_involutions (B : Fin 3 → Γ)
    (hB : Function.Injective B) (hmem : ∀ i, B i ∈ S) (hinvol : ∀ i, B i * B i = 1)
    (hsub : S ⊆ Set.range B) : BergeFulkerson (cayley S hSinv hS1) :=
  (cayley_properThreeEdgeColoring_of_involutions S hSinv hS1 B hB hmem hinvol hsub).bergeFulkerson






/-! ## A concrete infinite cubic Cayley graph: the ladder group `ℤ × ℤ/2` -/








/-! ## An infinite cubic Cayley graph on three involutions: the infinite dihedral group -/

open DihedralGroup












open Bridges.InfiniteCubicMatchings in
theorem solution: BergeFulkerson dihCayley := by
  refine cayley_bergeFulkerson_of_involutions _ _ _ ![sr 0, sr 1, sr 2] ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simp [dihGens]
  · intro i
    fin_cases i <;> simp [sr_mul_sr]
  · rintro x (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
