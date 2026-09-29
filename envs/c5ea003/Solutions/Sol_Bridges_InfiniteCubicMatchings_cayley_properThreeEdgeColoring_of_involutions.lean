-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.cayley_properThreeEdgeColoring_of_involutions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:45:27.129323+00:00
-- url     : https://prove2.me/submissions/59ce7f22-6618-4e62-9715-d93fa4114863

-- Sol generated from Bridges/InfiniteCubicMatchingsCayley.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
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
theorem solution(B : Fin 3 → Γ)
    (hB : Function.Injective B) (hmem : ∀ i, B i ∈ S) (hinvol : ∀ i, B i * B i = 1)
    (hsub : S ⊆ Set.range B) : ProperThreeEdgeColoring (cayley S hSinv hS1) := by
  refine ⟨fun i => cayleyInvolutionMatching S hSinv hS1 (B i) (hmem i) (hinvol i), ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    induction e with
    | _ x y =>
      rw [PerfectMatching.mem_edges] at hei hej
      exact absurd (hB (mul_left_cancel (hei.trans hej.symm))) hij
  · intro e
    induction e with
    | _ x y =>
      intro hE
      obtain ⟨i, hi⟩ := hsub (show x⁻¹ * y ∈ S from hE)
      refine ⟨i, ?_⟩
      rw [PerfectMatching.mem_edges]
      show x * B i = y
      rw [hi]
      group
