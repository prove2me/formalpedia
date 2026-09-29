-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Core
-- name    : Geometry_KernelPatterns_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:30.632925+00:00
-- url     : https://prove2.me/theorems/e49c538c-4810-4653-9c7c-402307ffbd4f
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Core.lean by skeleton subtraction
import Mathlib

/-!
# Kernel patterns of tuples: a complete invariant for the symmetric-group action

For a tuple `x : Fin n → X` its *kernel* is the equivalence relation
`i ~ j ↔ x i = x j` on the index set `Fin n`.  We encode it by the canonical
*pattern* `pat x : Fin n → Fin n`, sending `i` to the least index `j` with
`x j = x i` (the "first occurrence" representative).

Main results of this file.

* `pat_eq_iff` — `pat` faithfully records the kernel.
* `pat_congr`, `pat_comp_injective` — `pat` is invariant under post-composition
  by injective maps, in particular under the diagonal action of `Equiv.Perm X`.
* `exists_perm_of_pat_eq`, `perm_orbit_iff_pat_eq` — for a *finite* value type
  `X`, equality of patterns is *exactly* equality of `Sym(X)`-orbits, i.e. the
  kernel is a complete invariant of the symmetric-group action on `X ^ n`.
* `pat_not_complete_of_trivial_group` — sharpness: for a proper subgroup the
  kernel need not be a complete invariant.
* `pat_idem`, `mem_patterns_iff` — patterns are exactly the idempotent tuples
  `p : Fin n → Fin n` with `pat p = p`; consequently the set of patterns
  *stabilises*: `patterns n m = patterns n n` as soon as `n ≤ m`
  (`patterns_stabilise`).
-/

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X Y : Type*}

section Pat

variable [DecidableEq X]

/-- The *kernel pattern* of a tuple `x : Fin n → X`: the index `pat x i` is the
least `j` with `x j = x i`. -/
def pat (x : Fin n → X) (i : Fin n) : Fin n :=
  (univ.filter fun j => x j = x i).min' ⟨i, by simp⟩

lemma pat_mem (x : Fin n → X) (i : Fin n) :
    pat x i ∈ univ.filter fun j => x j = x i := Finset.min'_mem _ _

@[simp] lemma apply_pat (x : Fin n → X) (i : Fin n) : x (pat x i) = x i := by
  have := pat_mem x i; simpa using this


/-- Two tuples with the same kernel have the same pattern. -/
lemma pat_congr [DecidableEq Y] {x : Fin n → X} {y : Fin n → Y}
    (h : ∀ k l, x k = x l ↔ y k = y l) : pat x = pat y := by
  funext i
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simpa using (h _ _).2 (apply_pat y i))
  · exact Finset.min'_le _ _ (by simpa using (h _ _).1 (apply_pat x i))

/-- The pattern records the kernel faithfully. -/
@[simp] lemma pat_eq_iff {x : Fin n → X} {i j : Fin n} :
    pat x i = pat x j ↔ x i = x j := by
  constructor
  · intro h
    calc x i = x (pat x i) := (apply_pat x i).symm
      _ = x (pat x j) := by rw [h]
      _ = x j := apply_pat x j
  · intro h
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [h])
    · exact Finset.min'_le _ _ (by simp [h])



/-- The first-occurrence representative is a fixed point of the pattern map. -/
@[simp] lemma pat_apply_pat (x : Fin n → X) (i : Fin n) : pat x (pat x i) = pat x i :=
  pat_eq_iff.2 (apply_pat x i)

/-- Patterns are idempotent. -/
@[simp] lemma pat_idem (x : Fin n → X) : pat (pat x) = pat x :=
  pat_congr (fun _ _ => pat_eq_iff)

end Pat

/-! ### Completeness of the invariant for the symmetric group -/

section Complete

variable [Fintype X] [DecidableEq X]



end Complete


/-! ### The set of patterns, and stabilisation -/

/-- The finset of all kernel patterns of `n`-tuples with values in `Fin m`. -/
def patterns (n m : ℕ) : Finset (Fin n → Fin n) :=
  (univ : Finset (Fin n → Fin m)).image pat

/-- A tuple `p : Fin n → Fin n` is the pattern of some `Fin m`-valued tuple iff
it is idempotent and uses at most `m` distinct values. -/
lemma mem_patterns_iff {n m : ℕ} (p : Fin n → Fin n) :
    p ∈ patterns n m ↔ pat p = p ∧ (univ.image p).card ≤ m := by
  constructor
  · intro hp
    simp only [patterns, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨x, rfl⟩ := hp
    refine ⟨pat_idem x, ?_⟩
    have hfix : ∀ j ∈ univ.image (pat x), pat x j = j := by
      intro j hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
      obtain ⟨i, rfl⟩ := hj
      exact pat_eq_iff.2 (apply_pat x i)
    have hle : (univ.image (pat x)).card ≤ (univ.image x).card := by
      refine Finset.card_le_card_of_injOn (fun j => x j) (fun j _ => by simp) ?_
      intro j hj j' hj' hxx
      rw [← hfix j hj, ← hfix j' hj']
      exact pat_eq_iff.2 hxx
    exact hle.trans (by simpa using Finset.card_le_univ (univ.image x))
  · rintro ⟨hidem, hcard⟩
    have hcard' : Fintype.card ↥(univ.image p) ≤ Fintype.card (Fin m) := by
      rw [Fintype.card_coe, Fintype.card_fin]; exact hcard
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard'
    have hmem : ∀ i, p i ∈ univ.image p := fun i => Finset.mem_image_of_mem p (mem_univ i)
    refine Finset.mem_image.2 ⟨fun i => e ⟨p i, hmem i⟩, Finset.mem_univ _, ?_⟩
    have : pat (fun i => e ⟨p i, hmem i⟩) = pat p :=
      pat_congr (fun k l => by simp [e.injective.eq_iff, Subtype.ext_iff])
    rw [this, hidem]

lemma mem_patterns_self {n : ℕ} (p : Fin n → Fin n) :
    p ∈ patterns n n ↔ pat p = p := by
  rw [mem_patterns_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, by simpa using Finset.card_le_univ (univ.image p)⟩⟩


end Geometry.KernelPatterns


