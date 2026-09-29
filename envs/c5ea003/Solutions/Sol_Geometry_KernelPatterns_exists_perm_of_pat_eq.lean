-- Prove2me | solution 1 for Geometry.KernelPatterns.exists_perm_of_pat_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:20:20.377172+00:00
-- url     : https://prove2.me/submissions/6efe17b6-c7cf-401e-bed7-11f6bcceb1a2

-- Sol generated from Geometry/KernelPatterns/Core.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core

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

open Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X Y : Type*}


variable [DecidableEq X]












/-! ### Completeness of the invariant for the symmetric group -/


variable [Fintype X] [DecidableEq X]





/-! ### The set of patterns, and stabilisation -/






open Geometry.KernelPatterns in
theorem solution{x y : Fin n → X} (h : pat x = pat y) :
    ∃ σ : Equiv.Perm X, σ ∘ x = y := by
  classical
  have hxy : ∀ i j, x i = x j ↔ y i = y j := by
    intro i j
    rw [← pat_eq_iff (x := x), ← pat_eq_iff (x := y), h]
  set S : Set X := Set.range x with hS
  set T : Set X := Set.range y with hT
  let φ : S → T := fun a => ⟨y (Classical.choose a.2), Set.mem_range_self _⟩
  have hφ : ∀ a : S, x (Classical.choose a.2) = (a : X) := fun a => Classical.choose_spec a.2
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : y (Classical.choose a.2) = y (Classical.choose b.2) := congrArg Subtype.val hab
    have h2 := (hxy _ _).2 h1
    exact Subtype.ext (by rw [← hφ a, ← hφ b]; exact h2)
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨j, hj⟩ := b.2
    refine ⟨⟨x j, Set.mem_range_self j⟩, Subtype.ext ?_⟩
    have hx : x (Classical.choose (⟨x j, Set.mem_range_self j⟩ : S).2) = x j := hφ _
    simpa [φ, hj] using (hxy _ _).1 hx
  let e : S ≃ T := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have hcard : Fintype.card (Sᶜ : Set X) = Fintype.card (Tᶜ : Set X) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, Fintype.card_congr e]
  let e' : (Sᶜ : Set X) ≃ (Tᶜ : Set X) := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.Set.sumCompl S).symm.trans ((e.sumCongr e').trans (Equiv.Set.sumCompl T)), ?_⟩
  funext i
  have hmem : x i ∈ S := Set.mem_range_self i
  simp only [Function.comp_apply, Equiv.trans_apply,
    Equiv.Set.sumCompl_symm_apply_of_mem hmem, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl]
  have hval : (e ⟨x i, hmem⟩ : X) = y (Classical.choose (⟨x i, hmem⟩ : S).2) := rfl
  rw [hval]
  exact (hxy _ _).1 (hφ ⟨x i, hmem⟩)
