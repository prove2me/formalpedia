-- Prove2me | Theorems.Thm_ArgTop_fundamental_lemma
-- name    : ArgTop.fundamental_lemma
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:58:45.8174+00:00
-- url     : https://prove2.me/theorems/81583725-d95f-4945-81ed-32ddd3e6c5fe
-- title:
--   Dung's Fundamental Lemma (re-proved here to keep the file self-contained):
-- statement:
--   **Dung's Fundamental Lemma** (re-proved here to keep the file self-contained):
--   if `S` is admissible and defends `a`, then `insert a S` is admissible.
--
--   ```lean
--   theorem ArgTop.fundamental_lemma{S : Set A} (hS : Admissible R S) {a : A}
--       (ha : Defends R S a) : Admissible R (insert a S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ArgumentationCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ArgumentationCore.lean#L107

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

theorem ArgTop.fundamental_lemma{S : Set A} (hS : Admissible R S) {a : A}
    (ha : Defends R S a) : Admissible R (insert a S) := by sorry
