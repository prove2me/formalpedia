-- Prove2me | solution 1 for CWorldFiltration.exists_linear_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:57:54.150926+00:00
-- url     : https://prove2.me/submissions/985848e2-baa1-49ce-b3df-3338d242e481

-- Sol generated from Speculative/AutoResearch/CWorldFiltration.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CWorldFiltration
/-
# Clock-and-Switch Worlds: a Filtration / Representation Theorem

## What this file does

A **clock-and-switch world** `CWorld A B` is a pair consisting of a *clock reading*
`clock : A` and a *switch configuration* `switch : B → Bool`.  Accessibility is the
product order: the clock may only advance, and a switch that has been flipped on can
never be flipped off again.  This is the canonical "monotone resource" frame:
`CWorld (Fin n) (Fin m)` is the product of an `n`-chain with an `m`-dimensional
Boolean cube.

The mission was to prove the **filtration lemma**: every finite rooted directed
preorder is a bounded (`p`-)morphic image of some `CWorld (Fin n) (Fin m)`, extending
the two special cases `forgetSwitches` (project a world to its clock) and `cardChain`
(count the switches that are on).

The honest answer, established here, is a **sharp characterisation** rather than the
literal statement, and both halves are nontrivial:

* `antisymm_of_representable` (adversarial finding).  A bounded morphic image of a
  *finite partial order* is again antisymmetric.  Since every `CWorld (Fin n) (Fin m)`
  is a finite partial order, a finite preorder with a genuine two-element cluster is
  **never** such an image.  So the literal statement "every finite rooted directed
  *preorder*" is false, and the correct hypothesis is "rooted directed *poset*".
  The proof is not formal: it picks a maximal element of the (finite) preimage of the
  putative cluster and pushes it up with the back condition.

* `representable_of_rooted_directed` (main theorem).  Conversely, **every** finite
  rooted directed partial order `P` is a surjective bounded morphic image of
  `CWorld (Fin 1) (Fin (card P))`.  The morphism is the *greedy climb* `walk`: fix a
  linear extension `t 0, t 1, …` of `P` (Szpilrajn), start at the root, and read the
  switches left to right; when switch `i` is on, jump to `t i` if the current point
  still lies below `t i`, and otherwise jump to the top.  The "otherwise jump to the
  top" clause is exactly what makes the map monotone — the naive greedy walk without
  it is *not* monotone (see the Lab Notes below) — and the linear-extension property
  is exactly what makes it *open* (the back condition).

Combining the two halves gives `representable_iff`: for a finite preorder,

    representable by a clock-and-switch world  ↔  rooted ∧ directed ∧ antisymmetric.

The antisymmetry clause is removed again in `Combinatorics.CWorldClusterTolerant`, by
adjoining to the source an *indiscrete* phase coordinate; there the literal preorder
statement becomes true, and the number of phases needed is exactly the largest cluster
size of the target.

## Lab Notes (experimental data behind the theorems)

Exhaustive machine search over all labelled bounded posets (`= rooted + directed +
finite`) confirmed representability before the proof was attempted:

* all 36 bounded posets on 4 labelled points: representable, cube dimension `m ≤ 3`;
* all 380 bounded posets on 5 labelled points: representable, `m ≤ 4`;
* the 6-point "bowtie" `0 < a,b < c,d < 1` (not a lattice): representable with `m = 3`
  by `000↦0, 001↦c, 010↦a, 100↦b, 011↦c, 101↦c, 110↦d, 111↦1`.

Minimal cube dimensions found: 3-chain `m = 2`, 4-chain `m = 3`, 5-chain `m = 4`,
diamond `m = 2`, so `m` must be at least the height of `P` and at least `log₂ |P|`;
the theorem below spends `m = |P|`, which is not claimed to be optimal.

Counterexample hunt for monotonicity of the naive greedy walk (no "jump to the top"):
on the diamond `0 < a,b < 1` with linear extension `0,a,b,1`, switches `{b}` walk to
`b` while switches `{a,b}` walk to `a`, and `b ≰ a`.  This is the failure the `tp`
branch of `walk` repairs.

Every theorem below is proved with no `sorry` and no `native_decide`.
-/


open CWorldFiltration

open Function

attribute [local instance] Classical.propDecidable

/-! ## Part A — Clock-and-switch worlds -/


open CWorld

variable {A B : Type*}










/-! ## Part B — Bounded morphisms (p-morphisms) -/


open BddMorphism

variable {X Y Z : Type*} [Preorder X] [Preorder Y] [Preorder Z]







/-! ## Part C — The two catalogued special cases, and clock padding -/










/-! ## Part D — The greedy climb and the representation theorem -/




open walk

variable {P : Type*} [PartialOrder P] {t : ℕ → P} {r tp : P}











/-! ## Part E — The characterisation, and its consequences -/









instance : Nonempty Cluster := inferInstanceAs (Nonempty Bool)





open CWorldFiltration in
theorem solution(P : Type*) [PartialOrder P] [Fintype P] [Nonempty P] :
    ∃ (k : ℕ) (t : ℕ → P), (∀ p : P, ∃ j, j < k ∧ t j = p) ∧
      (∀ i j, i < k → j < k → t i ≤ t j → i ≤ j) ∧ k = Fintype.card P := by
  letI : Fintype (LinearExtension P) := inferInstanceAs (Fintype P)
  set k := Fintype.card P with hk
  have hcard : Fintype.card (LinearExtension P) = k := rfl
  let e : Fin k ≃o LinearExtension P := monoEquivOfFin (LinearExtension P) hcard
  refine ⟨k, fun i => if h : i < k then (id (e ⟨i, h⟩) : P) else Classical.arbitrary P, ?_, ?_, rfl⟩
  · intro p
    refine ⟨(e.symm (id p : LinearExtension P)).1, (e.symm _).2, ?_⟩
    simp [e]
  · intro i j hi hj hij
    simp only [dif_pos hi, dif_pos hj] at hij
    have h1 := toLinearExtension.monotone hij
    exact e.le_iff_le.mp h1
