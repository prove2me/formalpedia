-- Prove2me | solution 1 for Geometry.KernelPatterns.orbit_card_eq_card_patterns
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:23:19.010392+00:00
-- url     : https://prove2.me/submissions/18c2d885-6baa-4dc9-ab4f-fae91f6c8843

-- Sol generated from Geometry/KernelPatterns/Bell.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Theorems.Thm_Geometry_KernelPatterns_exists_perm_of_pat_eq
import Theorems.Thm_Geometry_KernelPatterns_pat_perm

/-!
# Counting kernel patterns: orbits, set partitions and the Bell numbers

Building on `Geometry.KernelPatterns.Core`, this file counts kernel patterns.

* `orbit_card_eq_card_patterns` — the number of `Sym(Fin m)`-orbits on the
  configuration space `(Fin m)^n` of `n`-tuples equals `(patterns n m).card`.
  (This is the counting form of the completeness theorem `perm_orbit_iff_pat_eq`.)
* `patternsEquivSetoid` — kernel patterns of length `n` are in bijection with
  equivalence relations (i.e. set partitions) on `Fin n`.
* `card_patterns_le_five` — the first six values of the pattern-counting
  sequence are the Bell numbers `1, 1, 2, 5, 15, 52` (OEIS A000110), agreeing
  with Mathlib's `Nat.bell`.
* `card_patterns_eq_sum_blocks` — the refinement of the count by the number of
  blocks.
-/

open Geometry.KernelPatterns

open Finset



/-! ### Orbit counting -/


variable (n m : ℕ)



/-! ### Patterns are set partitions -/



/-! ### Refining the count by the number of blocks -/


/-! ### The Bell numbers `1, 1, 2, 5, 15, 52` -/













open Geometry.KernelPatterns in
theorem solution:
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin m)) (Fin n → Fin m))
      = (patterns n m).card := by
  classical
  have hwd : ∀ x y : Fin n → Fin m,
      MulAction.orbitRel (Equiv.Perm (Fin m)) (Fin n → Fin m) x y →
        (⟨pat x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ : ↥(patterns n m))
          = ⟨pat y, Finset.mem_image_of_mem _ (Finset.mem_univ y)⟩ := by
    intro x y h
    obtain ⟨σ, hσ⟩ := h
    have hcomp : σ ∘ y = x := funext fun i => congrFun hσ i
    have hpat : pat x = pat y := by rw [← hcomp]; exact pat_perm σ y
    exact Subtype.ext hpat
  let f : MulAction.orbitRel.Quotient (Equiv.Perm (Fin m)) (Fin n → Fin m) →
      ↥(patterns n m) :=
    Quotient.lift (fun x => (⟨pat x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ :
      ↥(patterns n m))) hwd
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨x⟩ ⟨y⟩ hxy
      have hp : pat x = pat y := congrArg Subtype.val hxy
      obtain ⟨σ, hσ⟩ := exists_perm_of_pat_eq hp
      refine Quotient.sound ⟨σ⁻¹, funext fun i => ?_⟩
      have : σ (x i) = y i := congrFun hσ i
      simp [Equiv.Perm.smul_def, ← this]
    · rintro ⟨p, hp⟩
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨Quotient.mk _ x, rfl⟩
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_eq_finsetCard]
