-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.isLocalIsoAt_cayley
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:45:27.606989+00:00
-- url     : https://prove2.me/submissions/5812e8ca-f77e-4412-941f-a416f5a447e8

-- Sol generated from Bridges/InfiniteCubicMatchingsCayley.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
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












/-! ## A concrete infinite cubic Cayley graph: the ladder group `ℤ × ℤ/2` -/








/-! ## An infinite cubic Cayley graph on three involutions: the infinite dihedral group -/

open DihedralGroup












open Bridges.InfiniteCubicMatchings in
theorem solution(f : Γ →* Δ) (hinj : Set.InjOn f S)
    (hTinv : ∀ t ∈ f '' S, t⁻¹ ∈ f '' S) (hT1 : (1 : Δ) ∉ f '' S) (x : Γ) :
    IsLocalIsoAt (cayley S hSinv hS1) (cayley (f '' S) hTinv hT1) f x where
  adj := by
    intro y hy
    show (f x)⁻¹ * f y ∈ f '' S
    have : (f x)⁻¹ * f y = f (x⁻¹ * y) := by simp
    rw [this]
    exact ⟨_, hy, rfl⟩
  inj := by
    intro y z hy hz hfyz
    have h1 : f (x⁻¹ * y) = f (x⁻¹ * z) := by simp [hfyz]
    have := hinj hy hz h1
    exact mul_left_cancel this
  surj := by
    intro z hz
    obtain ⟨s, hs, hfs⟩ : (f x)⁻¹ * z ∈ f '' S := hz
    refine ⟨x * s, ?_, ?_⟩
    · show (x)⁻¹ * (x * s) ∈ S
      simpa using hs
    · have : f (x * s) = f x * f s := by simp
      rw [this, hfs]
      group
