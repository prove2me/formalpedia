-- Prove2me | Theorems.Thm_MultiverseModalForcing_meval_dia
-- name    : MultiverseModalForcing.meval_dia
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:38.688159+00:00
-- url     : https://prove2.me/theorems/7fc904e4-c706-4087-b506-047d4d344b19
-- title:
--   Diamond semantics.
-- statement:
--   **Diamond semantics.** `◇p` is true at `w` iff `p` holds in some forcing
--       extension of `w`.  This is the defining duality `◇p ↔ ¬□¬p`.
--
--   ```lean
--   theorem MultiverseModalForcing.meval_dia{α} (R : World α → World α → Prop) (M : Multiverse α)
--       (w : World α) (p : MSentence α) :
--       meval R M w (MSentence.dia p) ↔ ∃ v, R w v ∧ v ∈ M ∧ meval R M v p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/MultiverseModalForcing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/MultiverseModalForcing.lean#L112

-- Thm stub generated from Applications/ProofTheoryAndLogic/MultiverseModalForcing.lean
import Mathlib
import Definitions.Def_Applications_ProofTheoryAndLogic_MultiverseModalForcing
/-
# The Modal Logic of Forcing — a Kripke-semantic deepening of Multiverse Set Theory

This file equips the combinatorial core of the set-theoretic *multiverse* with a
**modal structure of forcing**, following the Hamkins–Löwe programme:

* **possibility** `◇p` — `p` holds in *some* forcing (generic) extension;
* **necessity**  `□p` — `p` holds in *every* forcing extension.

Forcing extensions form a Kripke *frame*: an accessibility relation `R` on worlds
(models of set theory).  We give the standard Kripke semantics for a language of
modal set-theoretic sentences and prove that the forcing frame is **sound for the
modal system `S4.2`**, the theorem at the heart of the modal logic of forcing:

* `sound_K`      — the distribution axiom `□(p → q) → (□p → □q)` (any frame);
* `sound_Nec`    — the necessitation rule (any frame);
* `sound_T`      — `□p → p` from **reflexivity** of forcing (you force over yourself);
* `sound_Four`   — `□p → □□p` from **transitivity** (iterated forcing);
* `sound_Two`    — `◇□p → □◇p` from **directedness** (any two extensions have a
  common further extension — the amalgamation/product-forcing property).

Together `K, T, 4, .2` axiomatise `S4.2`.  We also prove the **duality**
`◇p ↔ ¬□¬p`, monotonicity and distribution laws, package the result as
`forcing_sound_S42`, instantiate the abstract frame with a concrete
*flip-reachability* forcing frame over the multiverse, and finally show the logic
is **properly weaker than `S5`**: the characteristic axiom `B : p → □◇p` **fails**
in a directed reflexive-transitive forcing frame (`B_fails`).  Thus forcing is
genuinely `S4.2` and not `S5` — you cannot, in general, force your way back.

Everything is proved from first principles over `Mathlib`, self-contained.
-/

open MultiverseModalForcing

open Classical

/-! ## Worlds and modal sentences -/




open MSentence



/-! ## Kripke semantics for forcing

`R w v` reads "`v` is a forcing extension of `w`".  `M` is the multiverse of
admissible worlds.  `meval R M w p` is the truth of `p` at world `w`. -/









/-! ## Duality between necessity and possibility -/

theorem MultiverseModalForcing.meval_dia{α} (R : World α → World α → Prop) (M : Multiverse α)
    (w : World α) (p : MSentence α) :
    meval R M w (MSentence.dia p) ↔ ∃ v, R w v ∧ v ∈ M ∧ meval R M v p := by sorry
