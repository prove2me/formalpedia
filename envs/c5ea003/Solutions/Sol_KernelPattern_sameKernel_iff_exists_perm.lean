-- Prove2me | solution 1 for KernelPattern.sameKernel_iff_exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:06:15.070537+00:00
-- url     : https://prove2.me/submissions/b684d170-bb78-4b06-8ae2-a15c1e6dd64b

-- Sol generated from Algebra/KernelPatterns/Core.lean
import Mathlib
import Definitions.Def_Algebra_KernelPatterns_Core
import Theorems.Thm_KernelPattern_SameKernel_symm
import Theorems.Thm_KernelPattern_sameKernel_perm_comp
/-
# Kernel patterns of tuples: canonical form, invariance and completeness

For a tuple `x : Fin n → α` the *kernel* (or *equality pattern*) of `x` is the
equivalence relation `i ~ j ↔ x i = x j` on the index set `Fin n`.  This file
develops a computable canonical form for the kernel,

`canon x i = min { j | x j = x i }`,

and proves the two facts that make the kernel a *complete invariant* for the
action of the symmetric group `Equiv.Perm α` on tuples by postcomposition:

* `KernelPattern.canon_comp_of_injective` — the kernel is invariant: relabelling
  the values by an injection (in particular by a permutation) does not change it;
* `KernelPattern.sameKernel_iff_exists_perm` — the kernel is complete: two tuples
  with the same kernel differ by a permutation of `α`.

We also characterise the range of `canon` as the set of *idempotent contracting
retractions* `p : Fin n → Fin n` (`p i ≤ i` and `p (p i) = p i`), i.e. the
restricted-growth encodings of set partitions, and package it as the type
`KernelPattern.Pattern n`, which is a `Fintype` with decidable equality.
-/

open KernelPattern

variable {α β : Type*} {n : ℕ}

/-! ## The kernel relation -/







/-! ## The canonical form -/


variable [DecidableEq α] [DecidableEq β]









/-! ## Invariance under relabelling of the values -/



/-! ## Completeness of the invariant -/


/-! ## Patterns: the range of `canon` -/






instance : Fintype (Pattern n) := Subtype.fintype _






open KernelPattern in
theorem solution[Finite α] {x y : Fin n → α} :
    SameKernel x y ↔ ∃ σ : Equiv.Perm α, σ ∘ x = y := by
  classical
  constructor
  · intro h
    set S : Finset α := Finset.image x Finset.univ with hS
    set T : Finset α := Finset.image y Finset.univ with hT
    have hxmem : ∀ a : {a : α // a ∈ S}, ∃ i, x i = a.1 := by
      rintro ⟨a, ha⟩
      simpa [hS] using Finset.mem_image.mp ha
    choose idx hidx using hxmem
    have hmemT : ∀ a : {a : α // a ∈ S}, y (idx a) ∈ T := by
      intro a; simp [hT]
    let f : {a : α // a ∈ S} → {b : α // b ∈ T} := fun a => ⟨y (idx a), hmemT a⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have hy : y (idx a) = y (idx b) := congrArg Subtype.val hab
      have hx : x (idx a) = x (idx b) := (h (idx a) (idx b)).2 hy
      exact Subtype.ext (by rw [← hidx a, ← hidx b, hx])
    have hsurj : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
      have hmem : x i ∈ S := by simp [hS]
      refine ⟨⟨x i, hmem⟩, ?_⟩
      have hxx : x (idx ⟨x i, hmem⟩) = x i := hidx ⟨x i, hmem⟩
      have hy : y (idx ⟨x i, hmem⟩) = y i := (h _ _).1 hxx
      exact Subtype.ext (by simp only [f, hy, hi])
    let e : {a : α // a ∈ S} ≃ {b : α // b ∈ T} := Equiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨Equiv.extendSubtype e, ?_⟩
    funext i
    have hmem : x i ∈ S := by simp [hS]
    have h1 : (Equiv.extendSubtype e) (x i) = (e ⟨x i, hmem⟩ : α) :=
      Equiv.extendSubtype_apply_of_mem e _ hmem
    have hxx : x (idx ⟨x i, hmem⟩) = x i := hidx ⟨x i, hmem⟩
    have h2 : y (idx ⟨x i, hmem⟩) = y i := (h _ _).1 hxx
    simp only [Function.comp_apply, h1]
    change (f ⟨x i, hmem⟩ : α) = y i
    simpa [f] using h2
  · rintro ⟨σ, rfl⟩
    exact (sameKernel_perm_comp σ x).symm
