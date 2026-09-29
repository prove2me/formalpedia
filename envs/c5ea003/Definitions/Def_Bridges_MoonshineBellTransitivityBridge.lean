-- Prove2me | Definitions.Def_Bridges_MoonshineBellTransitivityBridge
-- name    : Bridges_MoonshineBellTransitivityBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:33.765991+00:00
-- url     : https://prove2.me/theorems/23967d8b-e0f5-42f8-8eae-23cdc0277e84
-- title:
--   Aether Catalog definitions — Bridges_MoonshineBellTransitivityBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MoonshineBellTransitivityBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MoonshineBellTransitivityBridge.lean by skeleton subtraction
import Mathlib

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

namespace MoonshineBell

open MulAction Function

/-! ## Part 1: Burnside's lemma and the moment hierarchy (self-contained restatement) -/

section Burnside

variable (G : Type*) [Group G] [Fintype G] (X : Type*) [MulAction G X] [Finite X]


end Burnside

section Moments

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

/-- Fixed points on the `k`-fold power are `k`-tuples of fixed points. -/
def fixedByPiEquiv (k : ℕ) (g : G) :
    fixedBy (Fin k → X) g ≃ (Fin k → fixedBy X g) where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun y := ⟨fun i => (y i).1, funext fun i => (y i).2⟩
  left_inv _ := by ext i; rfl
  right_inv _ := by ext i; rfl


variable (G X)


end Moments

/-! ## Part 2: patterns (restricted growth functions) and Bell numbers -/

/-- A *pattern*, i.e. a restricted growth function: an idempotent, index-non-increasing self-map
of `Fin k`.  Patterns are in canonical bijection with the set partitions of `Fin k`: `p i` is the
least element of the block of `i`. -/
def IsPattern {k : ℕ} (p : Fin k → Fin k) : Prop := (∀ i, p i ≤ i) ∧ ∀ i, p (p i) = p i

instance {k : ℕ} (p : Fin k → Fin k) : Decidable (IsPattern p) := by
  unfold IsPattern; infer_instance

/-- The type of patterns on `Fin k`; a finite decidable type modelling set partitions. -/
def Pattern (k : ℕ) : Type := {p : Fin k → Fin k // IsPattern p}

instance (k : ℕ) : Fintype (Pattern k) := by unfold Pattern; infer_instance
instance (k : ℕ) : DecidableEq (Pattern k) := by unfold Pattern; infer_instance

/-- The `k`-th Bell number, defined as the number of patterns (set partitions) on `Fin k`. -/
def bell (k : ℕ) : ℕ := Fintype.card (Pattern k)




/-! ## Part 3: the kernel pattern of a tuple -/

section Kernel

variable {X : Type*} {k : ℕ} {f f' : Fin k → X}

/-- The kernel pattern of a tuple `f : Fin k → X`: the least index taking the same value. -/
noncomputable def kerPat {k : ℕ} (f : Fin k → X) (i : Fin k) : Fin k :=
  haveI := Classical.decEq X
  (Finset.univ.filter (fun j => f j = f i)).min' ⟨i, by simp⟩

theorem kerPat_apply_eq (f : Fin k → X) (i : Fin k) : f (kerPat f i) = f i := by
  classical
  have h := Finset.min'_mem (Finset.univ.filter (fun j => f j = f i)) ⟨i, by simp⟩
  simpa [kerPat, Finset.mem_filter] using h

theorem kerPat_le (f : Fin k → X) (i : Fin k) : kerPat f i ≤ i := by
  classical
  exact Finset.min'_le _ _ (by simp)

/-- The kernel pattern only depends on the equality pattern of the tuple. -/
theorem kerPat_congr (h : ∀ i j, f i = f j ↔ f' i = f' j) : kerPat f = kerPat f' := by
  classical
  funext i
  have : (Finset.univ.filter (fun j => f j = f i))
      = (Finset.univ.filter (fun j => f' j = f' i)) := by
    ext j; simp [Finset.mem_filter, h j i]
  simp only [kerPat]
  congr 1

/-- Two coordinates get the same kernel representative exactly when the tuple agrees on them:
the kernel pattern is a *complete* invariant of the equality pattern. -/
theorem kerPat_eq_iff (f : Fin k → X) (i j : Fin k) :
    kerPat f i = kerPat f j ↔ f i = f j := by
  classical
  constructor
  · intro h
    have h1 := kerPat_apply_eq f i
    have h2 := kerPat_apply_eq f j
    rw [← h1, ← h2, h]
  · intro h
    have : (Finset.univ.filter (fun l => f l = f i))
        = (Finset.univ.filter (fun l => f l = f j)) := by
      ext l; simp [Finset.mem_filter, h]
    simp only [kerPat]
    congr 1

theorem kerPat_idem (f : Fin k → X) (i : Fin k) : kerPat f (kerPat f i) = kerPat f i :=
  (kerPat_eq_iff f _ i).2 (kerPat_apply_eq f i)

theorem isPattern_kerPat (f : Fin k → X) : IsPattern (kerPat f) :=
  ⟨kerPat_le f, kerPat_idem f⟩



variable {G : Type*} [Group G] [MulAction G X]

/-- The kernel pattern is a `G`-invariant of a tuple. -/
theorem kerPat_smul (g : G) (f : Fin k → X) : kerPat (g • f) = kerPat f :=
  kerPat_congr fun i j => by
    show g • f i = g • f j ↔ f i = f j
    exact smul_left_cancel_iff g

end Kernel

/-! ## Part 4: extending injective partial tuples -/



/-! ## Part 5: `k`-transitivity and orbits of tuples -/

section Transitivity

variable (k : ℕ) (G : Type*) [Group G] (X : Type*) [MulAction G X]

/-- `k`-transitivity: the group acts transitively on injective `k`-tuples. -/
def KTransitive : Prop :=
  ∀ f f' : Fin k → X, Injective f → Injective f' → ∃ g : G, g • f = f'

variable {k G X}


end Transitivity

/-! ## Part 6: the orbit–pattern correspondence -/

section OrbitPattern

variable {k : ℕ} {G : Type*} [Group G] {X : Type*} [MulAction G X]

/-- The kernel pattern descends to the orbit space of `k`-tuples. -/
noncomputable def orbitPattern : orbitRel.Quotient G (Fin k → X) → Pattern k :=
  Quotient.lift (fun f => (⟨kerPat f, isPattern_kerPat f⟩ : Pattern k)) <| by
    intro a b hab
    have hmem : a ∈ orbit G b := (orbitRel_apply).1 hab
    obtain ⟨g, hg⟩ := hmem
    have : kerPat a = kerPat b := by
      rw [← hg]; exact kerPat_smul g b
    exact Subtype.ext this




variable (k G X)



end OrbitPattern

/-! ## Part 7: the moment form — Bell numbers as extremal values of trace moments -/

section MomentCriterion

variable (k : ℕ) (G : Type*) [Group G] [Fintype G] (X : Type*) [MulAction G X] [Finite X]






end MomentCriterion

/-! ## Part 9: the extremal example — full symmetric groups attain the Bell bound -/

section Symmetric



end Symmetric

/-! ## Part 10: monotonicity of the hierarchy -/

section Monotone

variable {X : Type*} {k : ℕ}


variable (G : Type*) [Group G] [MulAction G X]



end Monotone

/-! ## Part 8: the graded (q-series) form -/

section Graded

variable (G : Type*) [Group G] [Fintype G] (Y : ℕ → Type*) [∀ n, MulAction G (Y n)]
  [∀ n, Finite (Y n)]

/-- The trace ("McKay–Thompson"-type) series of `g`: the `n`-th coefficient is the number of
points of grade `n` fixed by `g`. -/
noncomputable def traceSeries (g : G) : ℕ → ℕ := fun n => Nat.card (fixedBy (Y n) g)




end Graded

end MoonshineBell


