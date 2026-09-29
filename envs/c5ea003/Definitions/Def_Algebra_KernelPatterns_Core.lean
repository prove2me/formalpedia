-- Prove2me | Definitions.Def_Algebra_KernelPatterns_Core
-- name    : Algebra_KernelPatterns_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:21:21.047652+00:00
-- url     : https://prove2.me/theorems/70576084-2e72-46c5-aace-1839aa6af4a8
-- title:
--   Aether Catalog definitions — Algebra_KernelPatterns_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.KernelPatterns.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/KernelPatterns/Core.lean by skeleton subtraction
import Mathlib
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

namespace KernelPattern

variable {α β : Type*} {n : ℕ}

/-! ## The kernel relation -/

/-- Two tuples (possibly with values in different types) have the *same kernel*
when they realise the same equalities between coordinates. -/
def SameKernel (x : Fin n → α) (y : Fin n → β) : Prop := ∀ i j, x i = x j ↔ y i = y j




/-- The kernel relation of a tuple, as a `Setoid` on the index set. -/
def kerSetoid (x : Fin n → α) : Setoid (Fin n) where
  r i j := x i = x j
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩


/-! ## The canonical form -/

/-- Equal finsets have equal minima (the nonemptiness proofs are irrelevant). -/
private theorem min'_congr' {s t : Finset (Fin n)} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : s = t) : s.min' hs = t.min' ht := by subst h; rfl

variable [DecidableEq α] [DecidableEq β]

/-- The canonical representative of the kernel of `x`: `canon x i` is the least
index carrying the same value as `i`. -/
def canon (x : Fin n → α) (i : Fin n) : Fin n :=
  (Finset.univ.filter fun j => x j = x i).min' ⟨i, by simp⟩

theorem canon_mem (x : Fin n → α) (i : Fin n) :
    canon x i ∈ Finset.univ.filter fun j => x j = x i :=
  Finset.min'_mem _ _

/-- The canonical index carries the same value. -/
@[simp] theorem apply_canon (x : Fin n → α) (i : Fin n) : x (canon x i) = x i := by
  have := canon_mem x i
  simpa using this

theorem canon_le (x : Fin n → α) (i : Fin n) : canon x i ≤ i :=
  Finset.min'_le _ _ (by simp)

theorem canon_le_of_eq {x : Fin n → α} {i j : Fin n} (h : x j = x i) : canon x i ≤ j :=
  Finset.min'_le _ _ (by simp [h])

/-- Equality of canonical indices detects equality of values. -/
theorem canon_eq_iff (x : Fin n → α) (i j : Fin n) : canon x i = canon x j ↔ x i = x j := by
  constructor
  · intro h
    calc x i = x (canon x i) := (apply_canon x i).symm
    _ = x (canon x j) := by rw [h]
    _ = x j := apply_canon x j
  · intro h
    have hset : (Finset.univ.filter fun k => x k = x i)
        = Finset.univ.filter fun k => x k = x j := by
      ext k; simp [h]
    unfold canon
    exact min'_congr' _ _ hset

@[simp] theorem canon_idem (x : Fin n → α) (i : Fin n) : canon x (canon x i) = canon x i :=
  (canon_eq_iff x _ _).2 (apply_canon x i)

/-- The canonical form is a complete encoding of the kernel. -/
theorem sameKernel_iff_canon_eq {x : Fin n → α} {y : Fin n → β} :
    SameKernel x y ↔ canon x = canon y := by
  constructor
  · intro h
    funext i
    have hset : (Finset.univ.filter fun j => x j = x i) =
        Finset.univ.filter fun j => y j = y i := by
      ext k; simp [h k i]
    unfold canon
    exact min'_congr' _ _ hset
  · intro h i j
    rw [← canon_eq_iff x i j, ← canon_eq_iff y i j, h]

/-! ## Invariance under relabelling of the values -/

/-- The canonical form — hence the kernel — is invariant under an injective
relabelling of the values. -/
theorem canon_comp_of_injective {f : α → β} (hf : Function.Injective f)
    (x : Fin n → α) : canon (f ∘ x) = canon x := by
  funext i
  have hset : (Finset.univ.filter fun j => (f ∘ x) j = (f ∘ x) i) =
      Finset.univ.filter fun j => x j = x i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun h => hf h, fun h => congrArg f h⟩
  unfold canon
  exact min'_congr' _ _ hset


/-! ## Completeness of the invariant -/


/-! ## Patterns: the range of `canon` -/

/-- A *pattern* on `n` letters: an idempotent contracting retraction of `Fin n`.
These are exactly the canonical forms of kernels, i.e. the restricted-growth
encodings of set partitions of `Fin n`. -/
def IsPattern (p : Fin n → Fin n) : Prop := ∀ i, p i ≤ i ∧ p (p i) = p i

instance (p : Fin n → Fin n) : Decidable (IsPattern p) := by
  unfold IsPattern; infer_instance

theorem isPattern_canon (x : Fin n → α) : IsPattern (canon x) :=
  fun i => ⟨canon_le x i, canon_idem x i⟩

/-- Every pattern is its own canonical form: `canon` is a retraction onto the
patterns. -/
theorem canon_eq_self_of_isPattern {p : Fin n → Fin n} (hp : IsPattern p) : canon p = p := by
  funext i
  apply le_antisymm
  · exact canon_le_of_eq (hp i).2
  · have h1 : p (canon p i) = p i := apply_canon p i
    calc p i = p (canon p i) := h1.symm
    _ ≤ canon p i := (hp _).1

/-- The type of patterns on `n` letters. -/
def Pattern (n : ℕ) : Type := {p : Fin n → Fin n // IsPattern p}

instance : DecidableEq (Pattern n) := Subtype.instDecidableEq
instance : Fintype (Pattern n) := Subtype.fintype _

/-- The pattern of a tuple. -/
def patternOf (x : Fin n → α) : Pattern n := ⟨canon x, isPattern_canon x⟩

@[simp] theorem patternOf_val (x : Fin n → α) : (patternOf x).1 = canon x := rfl



end KernelPattern


