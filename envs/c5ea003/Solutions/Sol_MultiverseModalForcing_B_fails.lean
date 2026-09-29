-- Prove2me | solution 1 for MultiverseModalForcing.B_fails
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:29:43.020397+00:00
-- url     : https://prove2.me/submissions/c77b4be9-b6ff-4b4a-ade3-f887d9862525

-- Sol generated from Applications/ProofTheoryAndLogic/MultiverseModalForcing.lean
import Mathlib
import Definitions.Def_Applications_ProofTheoryAndLogic_MultiverseModalForcing
import Theorems.Thm_MultiverseModalForcing_meval_dia
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



/-! ## Soundness of the modal system S4.2 for forcing frames

We isolate the three frame conditions that forcing satisfies and show each
validates the corresponding modal axiom. -/









/-! ## Derived modal principles -/






/-! ## Packaging the S4.2 soundness theorem -/



/-! ## A concrete forcing frame: flip-reachability

We model a generic extension deciding an atom the other way by *flipping* its
truth value.  Two worlds are mutually accessible when they differ on only
finitely many atoms — the reachable class under finitely many forcing steps. -/







/-! ## Properness: forcing is `S4.2`, not `S5`

The characteristic `S5` axiom `B : p → □◇p` fails in a directed reflexive
transitive forcing frame.  Hence the modal logic of forcing is *properly* weaker
than `S5`: from a generic extension you cannot in general force *back* to the
ground model. -/









/-! ## Independence recast modally

The multiverse notion of *independence* (true in some world, false in another)
is exactly modal *contingency* `◇p ∧ ◇¬p` under the full-accessibility frame.  We
record the modal reading and a concrete instance. -/


open Claim





/-! ## Bridge: modal contingency = multiverse independence

The base multiverse file calls a sentence **independent** in `M` when it is true
in some admissible world and false in another.  Here we show this is *exactly*
modal **contingency** `◇p ∧ ◇¬p` in the **full-accessibility** forcing frame,
where every admissible world is a forcing extension of every other.  This closes
the conceptual gap between the two files with a single general theorem. -/







open MultiverseModalForcing in
theorem solution:
    ¬ MValid sinkFrame.R sinkFrame.M
        (.imp (.atom true) (.box (MSentence.dia (.atom true)))) := by
  intro h
  -- `p → □◇p` at `wT`
  have key : meval sinkFrame.R sinkFrame.M wT
      (.imp (.atom true) (.box (MSentence.dia (.atom true)))) := h wT trivial
  -- `p` is true at `wT`
  have hp : meval sinkFrame.R sinkFrame.M wT (.atom true) := by
    simp [meval, wT]
  -- so `□◇p` holds at `wT`; specialise to the accessible sink `wF`
  have hbox := key hp
  have hwF : sinkFrame.R wT wF := Or.inl rfl
  have hdia : meval sinkFrame.R sinkFrame.M wF (MSentence.dia (.atom true)) :=
    hbox wF hwF trivial
  rw [meval_dia] at hdia
  obtain ⟨u, hRu, _, hpu⟩ := hdia
  -- `wF` is a sink, so `u = wF`, but the atom is false there
  have : u = wF := by
    rcases hRu with h1 | h1
    · exact h1
    · exact h1 ▸ rfl
  subst this
  simp [meval, wF] at hpu
