-- Prove2me | solution 1 for CWorldFiltration.walk.open_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:57:55.614088+00:00
-- url     : https://prove2.me/submissions/11bbc78a-d775-4732-98fb-f54ca4513d85

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


theorem succ (s : ℕ → Bool) (i : ℕ) :
    walk t r tp s (i + 1) =
      if s i = true then (if walk t r tp s i ≤ t i then t i else tp) else walk t r tp s i := by
  rw [walk]

/-- The climb after `i` steps only depends on the first `i` switches. -/
theorem congr_of_eq {s s' : ℕ → Bool} {i : ℕ} (h : ∀ l, l < i → s l = s' l) :
    walk t r tp s i = walk t r tp s' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hi := ih fun l hl => h l (by omega)
      rw [succ, succ, hi, h i (by omega)]








/-! ## Part E — The characterisation, and its consequences -/









instance : Nonempty Cluster := inferInstanceAs (Nonempty Bool)





open CWorldFiltration.walk in
theorem solution(htop : ∀ p : P, p ≤ tp) {k : ℕ}
    (hlin : ∀ i j, i < k → j < k → t i ≤ t j → i ≤ j) :
    ∀ (i : ℕ), i ≤ k → ∀ (s : ℕ → Bool) (j : ℕ), j < i → walk t r tp s i ≤ t j →
      ∃ s' : ℕ → Bool, (∀ l, s l = true → s' l = true) ∧ (∀ l, i ≤ l → s' l = s l) ∧
        walk t r tp s' i = t j := by
  intro i
  induction i with
  | zero => intro _ s j hj; omega
  | succ i ih =>
      intro hik s j hj hq
      have hik' : i < k := by omega
      rw [succ] at hq
      by_cases hs : s i = true
      · rw [if_pos hs] at hq
        by_cases hb : walk t r tp s i ≤ t i
        · rw [if_pos hb] at hq
          have hij : i ≤ j := hlin i j hik' (by omega) hq
          have hji : j = i := by omega
          exact ⟨s, fun _ h => h, fun _ _ => rfl, by rw [succ, if_pos hs, if_pos hb, hji]⟩
        · rw [if_neg hb] at hq
          have hqe : t j = tp := le_antisymm (htop _) hq
          exact ⟨s, fun _ h => h, fun _ _ => rfl, by rw [succ, if_pos hs, if_neg hb, hqe]⟩
      · rw [if_neg hs] at hq
        by_cases hji : j < i
        · obtain ⟨s'', h1, h2, h3⟩ := ih (by omega) s j hji hq
          refine ⟨s'', h1, fun l hl => h2 l (by omega), ?_⟩
          rw [succ, h2 i (le_refl i), if_neg hs, h3]
        · have hji' : j = i := by omega
          subst hji'
          refine ⟨Function.update s j true, ?_, ?_, ?_⟩
          · intro l hl
            by_cases h : l = j
            · subst h; simp
            · simpa [Function.update_of_ne h] using hl
          · intro l _
            exact Function.update_of_ne (by omega) _ _
          · have hw : walk t r tp (Function.update s j true) j = walk t r tp s j :=
              (congr_of_eq fun l hl => (Function.update_of_ne (by omega) _ _).symm).symm
            rw [succ, hw]
            simp [hq]
