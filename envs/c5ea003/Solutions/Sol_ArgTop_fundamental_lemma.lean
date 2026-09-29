-- Prove2me | solution 1 for ArgTop.fundamental_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T19:12:15.466388+00:00
-- url     : https://prove2.me/submissions/54e0c755-a8c1-4d2b-87a2-a8e336d78e83

-- Thm stub generated from Novelty/ArgumentationExtensions.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationExtensions

/-!
# The topology of argumentation, II: preferred and grounded extensions

This file is **self-contained** (it re-declares the basic Dung semantics from
`ArgumentationCore`) and develops the two central *extension-based* semantics of
an argumentation framework `(A, R)`:

* `Preferred S` — `S` is a **preferred extension**: a *maximal* admissible set.
* `Complete S`  — `S` is a **complete extension**: admissible and closed under
  the defense operator (`charF S ⊆ S`).
* `groundedExt` — the **grounded extension**: the *least* fixed point of the
  defense operator (skeptical semantics).

Main results:

* `admissible_sUnion_chain`   — admissible sets are closed under unions of chains.
* `exists_preferred_superset` — (Zorn) every admissible set extends to a
  preferred extension; in particular `exists_preferred`.
* `preferred_complete`        — **every preferred extension is complete**
  (Dung); the proof is a direct application of the Fundamental Lemma.
* `groundedExt_subset_complete` / `groundedExt_subset_preferred` — the grounded
  extension is contained in every complete, hence every preferred, extension:
  the skeptically-accepted arguments are accepted under every credulous position.
-/

open ArgTop

variable {A : Type*} (R : A → A → Prop)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem e_fundamental_lemma {A : Type*} (R : A → A → Prop) {S : Set A}
    (hS : Admissible R S) {a : A} (ha : Defends R S a) : Admissible R (insert a S) := by
  obtain ⟨hcf, hdef⟩ := hS
  have hmono : ∀ {x : A}, Defends R S x → Defends R (insert a S) x := by
    intro x h b hb
    obtain ⟨c, hc, hcb⟩ := h b hb
    exact ⟨c, Or.inr hc, hcb⟩
  have hno : ∀ c ∈ S, ¬ R c a := by
    intro c hc hca
    obtain ⟨d, hd, hdc⟩ := ha c hca
    exact hcf d hd c hc hdc
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    rcases Set.mem_insert_iff.1 hx with hxa | hx
    · rcases Set.mem_insert_iff.1 hy with hya | hy
      · obtain ⟨c, hc, hca⟩ := ha a (by rw [hxa, hya] at hxy; exact hxy)
        exact hno c hc hca
      · obtain ⟨c, hc, hcx⟩ := hdef y hy a (by rw [hxa] at hxy; exact hxy)
        exact hno c hc hcx
    · rcases Set.mem_insert_iff.1 hy with hya | hy
      · exact hno x hx (by rw [hya] at hxy; exact hxy)
      · exact hcf x hx y hy hxy
  · intro x hx
    rcases Set.mem_insert_iff.1 hx with hxa | hx
    · rw [hxa]; exact hmono ha
    · exact hmono (hdef x hx)

theorem solution {S : Set A} (hS : Admissible R S) {a : A}
    (ha : Defends R S a) : Admissible R (insert a S) :=
  e_fundamental_lemma R hS ha
