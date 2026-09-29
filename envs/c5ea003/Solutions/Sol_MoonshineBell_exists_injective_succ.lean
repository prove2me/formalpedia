-- Prove2me | solution 1 for MoonshineBell.exists_injective_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:08:31.477257+00:00
-- url     : https://prove2.me/submissions/76a09d0d-9ed7-44fb-a63a-4dcf2974eda5

-- Sol generated from Bridges/MoonshineBellTransitivityBridge.lean
import Mathlib
import Definitions.Def_Bridges_MoonshineBellTransitivityBridge

/-!
# Moonshine beyond the j-function III: Bell numbers, moments of trace series, and
# `k`-transitivity

This file closes **Conjecture B** of the previous cycle of this research thread
(`Catalog/Bridges/MoonshineMomentLaurentBridge.lean`, `FUTURE_DIRECTIONS.md`), which asked
whether the `k`-th moment of the fixed-point ("permutation character" / trace) series of a
finite group action attains the value `B_k · |G|` — with `B_k` the `k`-th Bell number —
*exactly* for the `k`-transitive actions.  Cycle 1 proved only the case `k = 2`
(`sum_fixedPoints_sq_eq_two_mul_card_iff`).  Here the full statement is proved for every `k`.

## The bridge

Three a priori unrelated quantities are identified:

* **Character theory / moonshine side.**  The `k`-th moment `∑_{g∈G} |X^g|^k` of the family of
  trace series `T_g(q)` attached to a graded finite `G`-set.
* **Enumerative combinatorics side.**  The Bell number `B_k`, realized here as the number of
  *restricted growth functions* `p : Fin k → Fin k` (`IsPattern`: `p i ≤ i` and `p ∘ p = p`),
  a standard encoding of the set partitions of a `k`-element set.
* **Permutation group side.**  `k`-transitivity of the action.

The main results are:

* `bell_le_card_orbits` : `B_k ≤ #((Fin k → X)/G)` whenever `k ≤ |X|` — the number of orbits on
  `k`-tuples is always at least the number of set partitions of `{1,…,k}`, because the kernel
  pattern of a tuple is a complete `G`-invariant of "which coordinates agree".
* `bell_mul_card_le_sum_fixedPoints_pow` : consequently every moment of the trace family obeys
  the universal lower bound `B_k·|G| ≤ ∑_{g∈G}|X^g|^k`; Burnside's lemma (`k = 1`) is the
  degenerate case `B_1 = 1`.
* `card_orbits_eq_bell_iff` and `sum_fixedPoints_pow_eq_bell_mul_card_iff` : the bound is
  attained **iff the action is `k`-transitive**.  So a single integer moment of the
  moonshine-type trace family decides a purely group-theoretic transitivity property.
* `sum_traceSeries_pow_eq_bell_of_kTransitive` : the graded ("q-series") form — if every grade
  of a graded `G`-set is `k`-transitive, the coefficientwise `k`-th moment of the trace series
  is the constant series `B_k·|G|`.
* `perm_kTransitive` and `sum_fixedPoints_pow_perm` : the bound is attained — the full symmetric
  group of a finite set is `k`-transitive for every `k`, so `∑_{σ∈S_n}|fix σ|^k = B_k·n!`.
  In particular the criterion is not vacuous.
* `kTransitive_of_succ` and `sum_fixedPoints_pow_eq_bell_of_succ` : the hierarchy is decreasing,
  so extremality of one moment propagates downwards to all lower moments.

## Proof architecture

1. `kerPat f` is the canonical *kernel pattern* of a tuple `f : Fin k → X`: the `i`-th value is
   the least index `j` with `f j = f i`.  It is a restricted growth function
   (`isPattern_kerPat`), it is a complete invariant of the equality pattern of `f`
   (`kerPat_eq_iff`), and it is `G`-invariant (`kerPat_smul`).
2. `exists_injective_extension` : an injective partial tuple defined on a finset of indices
   extends to a globally injective tuple as soon as `k ≤ |X|`.  This is what makes the kernel
   pattern map *surjective* onto all patterns, and it is also the engine of step 3.
3. `exists_smul_eq_of_kerPat_eq` : for a `k`-transitive action, two tuples with the same kernel
   pattern lie in the same orbit — obtained by extending both tuples, restricted to their block
   leaders, to injective tuples and applying `k`-transitivity there.
4. Hence `orbitPattern : (Fin k → X)/G → Pattern k` is always surjective, and it is injective
   iff the action is `k`-transitive; comparing cardinalities gives the main theorems, which are
   then transported to the moment side through the moment identity
   `∑_g |X^g|^k = #((Fin k → X)/G)·|G|` (re-proved here so that the file is self-contained).

`Pattern k` is a decidable finite type, so the Bell numbers `1, 1, 2, 5, 15, 52`
(OEIS A000110) are verified by `decide` in `bell_zero` … `bell_five`; these are auxiliary
sanity checks, not the mathematical content.
-/

open MoonshineBell

open MulAction Function

/-! ## Part 1: Burnside's lemma and the moment hierarchy (self-contained restatement) -/


variable (G : Type*) [Group G] [Fintype G] (X : Type*) [MulAction G X] [Finite X]




variable {G : Type*} [Group G] {X : Type*} [MulAction G X]



variable (G X)



/-! ## Part 2: patterns (restricted growth functions) and Bell numbers -/




instance (k : ℕ) : DecidableEq (Pattern k) := by unfold Pattern; infer_instance





/-! ## Part 3: the kernel pattern of a tuple -/


variable {X : Type*} {k : ℕ} {f f' : Fin k → X}










variable {G : Type*} [Group G] [MulAction G X]



/-! ## Part 4: extending injective partial tuples -/



/-! ## Part 5: `k`-transitivity and orbits of tuples -/


variable (k : ℕ) (G : Type*) [Group G] (X : Type*) [MulAction G X]


variable {k G X}



/-! ## Part 6: the orbit–pattern correspondence -/


variable {k : ℕ} {G : Type*} [Group G] {X : Type*} [MulAction G X]





variable (k G X)




/-! ## Part 7: the moment form — Bell numbers as extremal values of trace moments -/


variable (k : ℕ) (G : Type*) [Group G] [Fintype G] (X : Type*) [MulAction G X] [Finite X]







/-! ## Part 9: the extremal example — full symmetric groups attain the Bell bound -/





/-! ## Part 10: monotonicity of the hierarchy -/


variable {X : Type*} {k : ℕ}


variable (G : Type*) [Group G] [MulAction G X]




/-! ## Part 8: the graded (q-series) form -/


variable (G : Type*) [Group G] [Fintype G] (Y : ℕ → Type*) [∀ n, MulAction G (Y n)]
  [∀ n, Finite (Y n)]







open MoonshineBell in
theorem solution[Finite X] (hk : k + 1 ≤ Nat.card X) (f : Fin k → X)
    (hf : Injective f) :
    ∃ F : Fin (k + 1) → X, Injective F ∧ ∀ i : Fin k, F i.castSucc = f i := by
  classical
  letI := Fintype.ofFinite X
  have hcard : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf]; simp
  have hne : ∃ y : X, y ∉ Finset.univ.image f := by
    by_contra hcon
    push_neg at hcon
    have huniv : (Finset.univ.image f) = Finset.univ := Finset.eq_univ_iff_forall.2 hcon
    rw [huniv, Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
    omega
  obtain ⟨y, hy⟩ := hne
  refine ⟨Fin.snoc f y, ?_, fun i => by simp⟩
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast j =>
      exfalso
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
      exact hy (Finset.mem_image.2 ⟨j, Finset.mem_univ j, hab.symm⟩)
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      exfalso
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
      exact hy (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hab⟩)
    | cast j =>
      simp only [Fin.snoc_castSucc] at hab
      rw [hf hab]
