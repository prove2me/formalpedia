-- Prove2me | solution 1 for TemporalGL.loeb_box_sound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:59:32.727888+00:00
-- url     : https://prove2.me/submissions/b31632f9-c794-4f59-8303-b37c4dc6bbb5

-- Sol generated from Logic/PosetTheory/TemporalGL.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL

/-!
# Temporal Gödel–Löb Logic (TGL): When You Prove Something Matters

Standard provability logic treats proofs as timeless: once a sentence is provable,
it is provable forever, and the modal `□` (Gödel–Löb provability) carries no temporal
information. In practice, proofs are *discovered in time*, and the order of discovery
forms a causal structure. This file formalises a **temporal extension of Gödel–Löb
logic GL** in which provability is indexed by a discrete time `t : ℕ` ("provably
established by time `t`") and a temporal order `T` records the flow of time.

The development has two complementary layers.

* A **semantic (Kripke) layer**: a `TempFrame` bundles a GL accessibility relation
  `R` (transitive + converse well-founded — the structure that validates Löb) with a
  temporal preorder `T` and a *monotonicity-in-time* compatibility condition `compat`
  (provability only grows as time passes). On these frames we prove soundness of the
  GL axioms together with the new temporal interaction axiom and the central temporal
  facts about proof discovery.

* An **algebraic (arithmetical) layer**: a `TempProv` structure axiomatises a
  *time-stamped provability predicate* `prov t A` ("there is a proof of `A`
  established by stage `t`") with persistence, modus ponens, Σ₁-completeness
  (positive introspection) and Löb. This is the abstract target of arithmetical
  completeness over Peano Arithmetic.

## Catalog synthesis

This module **extends** the catalog's provability-logic development:

* `Catalog/Logic/ProvabilityLogic/GLPFrames.lean` (`GLPLogic.GLFrame`,
  `GLPLogic.loeb_valid`, `GLPLogic.second_incompleteness`) — we re-derive Löb
  soundness via converse-well-founded induction in the temporal setting
  (`loeb_box_sound`) and lift Gödel's second incompleteness theorem to the
  *semantic* statement that consistency is unprovable on any GL frame
  (`kripke_second_incompleteness`) and to a *time-stamped* algebraic form
  (`godel_second_at_time`).
* `Catalog/Logic/GLKripke.lean` (`GLFrame`, `gl_frame_validates_loeb`,
  `gl_frame_well_founded`, `gl_antireflexive`) — our `TempFrame` adds the temporal
  axes `T`/`compat` on top of the same GL-frame skeleton.
* `Catalog/Logic/FormalTime.lean` (`TemporalOrder`, clocks) — the temporal preorder
  `T` is the discrete, provability-relevant counterpart of that order-theoretic model
  of time.

## Theorem index (Step 1)

1. `loeb_box_sound` — Löb's axiom is sound on every temporal GL frame — **proved**
   (converse-well-founded induction; the heart of GL).
2. `four_box_sound` — the `4` axiom `□A → □□A` is sound (transitivity) — **proved**.
3. `tgl_axiom_sound` — the **temporal axiom** `□A → □□◇A` ("if provable now, then it
   is provably-provable that it will be provable") is sound — **proved**.
4. `provability_persists` — `□A → G □A`: what is provable now stays provable at all
   future times — **proved** (uses time-monotonicity `compat`).
5. `today_not_tomorrow_refuted` — the temporal paradox "provable today but *not*
   tomorrow" is refutable in TGL — **proved**.
6. `tomorrow_not_today_satisfiable` — its mirror "provable tomorrow but not today"
   is *satisfiable*, exposing the genuine temporal asymmetry of proof discovery —
   **proved** (explicit two-world model).
7. `kripke_second_incompleteness` — semantic Gödel II: on a GL frame, if a world is
   consistent then its consistency is not provable there — **proved** (well-founded
   maximal-world argument).
8. `godel_second_at_time` — time-stamped Gödel II: consistency at stage `t` implies
   "consistency-at-`t`" is not provable at stage `t` — **proved** (Löb).
9. `future_self_certification` — `prov t A → prov s (prov t A)` for `t ≤ s`: a proof
   established by time `t` is, at every later time, provably established — **proved**.
10. `trivialTempProv_consistent` — the axioms of `TempProv` are consistent (a model
    exists), so the Gödel results are not vacuous — **proved**.
11. `loeb_fails_with_reflexive` — boundary case: drop converse well-foundedness and
    Löb's axiom fails — **proved** (one reflexive world).
12. `provability_monotone` — restatement of persistence: proofs are never lost —
    **proved**.
-/

open TemporalGL

variable {W : Type*}

/-! ## Modal and temporal operators (shallow semantics)

We work with predicates `A : W → Prop` ("`A` holds at world `w`"). `Box R A` is the
GL provability box along the proof-accessibility relation `R`; `Glob T A` ("globally")
and `Fut T A` ("eventually") are the temporal `G`/`F` operators along the time order
`T`. The temporal diamond `◇` of the concept is `Fut`. -/





/-! ## Part 1 — Soundness of the GL axioms on temporal frames -/

-- !-- Löb's axiom by converse-well-founded induction on `R`: assuming `w ⊩ □(□A→A)`,
--     prove `A` holds at every `R`-successor `x` by induction; the IH gives `□A` at
--     `x`, and the hypothesis turns that into `A` at `x`. Extends `GLPLogic.loeb_valid`. -- !--

-- !-- The `4` axiom is pure transitivity: a successor of a successor is a successor. -- !--

-- !-- Temporal axiom `□A → □□◇A`. From `□A` and `R`-transitivity, `A` holds at every
--     `u` two `R`-steps out; reflexivity of time then witnesses `◇A` at `u` (take the
--     present moment). So provability now entails it is provably-provable that `A`
--     will be provable. -- !--

/-! ## Part 2 — Temporal dynamics of proof discovery -/

-- !-- Persistence of provability: by `compat`, every future `R`-successor was already
--     a present `R`-successor, so a present box survives into the future. -- !--

-- !-- "Provable today but not tomorrow" contradicts persistence: the future world
--     witnessing non-provability is reached by `T`, where `provability_persists`
--     forces provability. -- !--


-- !-- The mirror situation is realised in `boolTempFrame` with `A = (· = true)`:
--     today (`true`) has the bad successor `false`, so `A` is not provable; tomorrow
--     (`false`) is a dead end, so `A` is vacuously provable. -- !--

/-! ## Part 3 — Gödel's second incompleteness theorem, semantically and temporally -/

-- !-- Semantic Gödel II. Consistency at `w` = "`w` has an `R`-successor". By converse
--     well-foundedness pick an `R`-minimal successor `m`; transitivity forces `m` to be
--     a dead end, so `m` is *inconsistent* (no successor). Hence "consistency holds at
--     every successor" fails at `w`: consistency is unprovable. Strengthens
--     `GLPLogic.second_incompleteness` to the existential frame condition. -- !--

/-! ## Part 4 — The time-stamped provability predicate (algebraic layer) -/


-- !-- Time-stamped Gödel II: `¬ prov t False` is `prov t False → False`, so
--     `prov t (¬ prov t False)` is `prov t (prov t False → False)`; Löb (at `A = False`)
--     turns this into `prov t False`, contradicting consistency. -- !--

-- !-- Combine Σ₁-completeness (`prov t A → prov t (prov t A)`) with persistence
--     (`t ≤ s`) to push the certificate forward in time. -- !--

-- !-- Restatement of the `persist` field: provability is monotone in time. -- !--



/-! ## Part 5 — Boundary: why converse well-foundedness is essential -/

-- !-- One reflexive world `()` with `R = ⊤`. Then `□A → A` collapses to `A → A` (true),
--     so `□(□A→A)` holds, yet `□A = A = False` fails: Löb's axiom is invalid once the
--     converse-well-foundedness of `TempFrame.R_wf` is dropped. -- !--


open TemporalGL in
theorem solution(F : TempFrame) (A : F.W → Prop) (w : F.W)
    (h : Box F.R (fun v => Box F.R A v → A v) w) : Box F.R A w := by
  have key : ∀ v, F.R w v → A v := by
    intro v
    induction v using F.R_wf.induction with
    | _ x ih =>
      intro hwx
      exact h x hwx (fun u hxu => ih u hxu (F.R_trans hwx hxu))
  exact key
