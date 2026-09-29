-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Bell
-- name    : Geometry_KernelPatterns_Bell
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:29.795599+00:00
-- url     : https://prove2.me/theorems/72933d28-02ff-4b62-adca-5cab43fc1151
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Bell
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Bell`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Bell.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core

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

namespace Geometry.KernelPatterns

open Finset

/-- Kernel patterns of `n`-tuples using exactly `k` distinct values (i.e. set
partitions of `Fin n` into exactly `k` blocks). -/
def patternsWith (n k : ℕ) : Finset (Fin n → Fin n) :=
  (patterns n n).filter fun p => (univ.image p).card = k


/-! ### Orbit counting -/

section Orbits

variable (n m : ℕ)


end Orbits

/-! ### Patterns are set partitions -/

/-- The kernel of a tuple, as an equivalence relation on the index set. -/
def kerSetoid {n : ℕ} {X : Type*} (x : Fin n → X) : Setoid (Fin n) where
  r i j := x i = x j
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

open Classical in
/-- **Kernel patterns are exactly the set partitions of the index set**: the map
sending a pattern to its kernel relation is a bijection onto `Setoid (Fin n)`. -/
noncomputable def patternsEquivSetoid (n : ℕ) : ↥(patterns n n) ≃ Setoid (Fin n) where
  toFun p := kerSetoid (p : Fin n → Fin n)
  invFun s := ⟨pat (fun i => Quotient.mk s i), by
    rw [mem_patterns_self]; exact pat_idem _⟩
  left_inv := by
    rintro ⟨p, hp⟩
    rw [mem_patterns_self] at hp
    apply Subtype.ext
    show (pat fun i => Quotient.mk (kerSetoid p) i) = p
    have : pat (fun i => Quotient.mk (kerSetoid p) i) = pat p :=
      pat_congr fun k l => by
        constructor
        · intro h; exact Quotient.exact h
        · intro h; exact Quotient.sound h
    rw [this, hp]
  right_inv := by
    intro s
    have hiff : ∀ k l : Fin n,
        pat (fun i => Quotient.mk s i) k = pat (fun i => Quotient.mk s i) l ↔ s.r k l := by
      intro k l
      rw [pat_eq_iff]
      exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
    exact Setoid.ext hiff

/-! ### Refining the count by the number of blocks -/


/-! ### The Bell numbers `1, 1, 2, 5, 15, 52` -/












end Geometry.KernelPatterns


