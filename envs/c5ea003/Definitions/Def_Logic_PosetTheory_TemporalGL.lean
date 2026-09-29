-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalGL
-- name    : Logic_PosetTheory_TemporalGL
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:30.95249+00:00
-- url     : https://prove2.me/theorems/9200a0a8-eef1-430a-a5f7-8f2de882960c
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalGL
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalGL`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalGL.lean by skeleton subtraction
import Mathlib

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

namespace TemporalGL

variable {W : Type*}

/-! ## Modal and temporal operators (shallow semantics)

We work with predicates `A : W → Prop` ("`A` holds at world `w`"). `Box R A` is the
GL provability box along the proof-accessibility relation `R`; `Glob T A` ("globally")
and `Fut T A` ("eventually") are the temporal `G`/`F` operators along the time order
`T`. The temporal diamond `◇` of the concept is `Fut`. -/

/-- `Box R A w` : "`A` is provable from `w`", i.e. `A` holds at every `R`-successor. -/
def Box (R : W → W → Prop) (A : W → Prop) (w : W) : Prop := ∀ v, R w v → A v

/-- `Glob T A w` : "`A` holds at all future times" (the temporal `G`/`□ₜ`). -/
def Glob (T : W → W → Prop) (A : W → Prop) (w : W) : Prop := ∀ v, T w v → A v

/-- `Fut T A w` : "`A` will hold at some future time" (the temporal `F`/`◇ₜ`). -/
def Fut (T : W → W → Prop) (A : W → Prop) (w : W) : Prop := ∃ v, T w v ∧ A v

/-- A **temporal GL frame**: a Gödel–Löb accessibility relation `R` (transitive and
converse well-founded) together with a temporal preorder `T`, linked by the
*time-monotonicity* condition `compat`: anything accessible in the future was already
accessible now, i.e. the set of `R`-successors only shrinks as time advances, so
provability only grows. -/
structure TempFrame where
  /-- The worlds (consistent stages / partial completions). -/
  W : Type
  /-- Proof-accessibility: `R w v` means `v` is a counterexample world reachable from `w`. -/
  R : W → W → Prop
  /-- Temporal order: `T w w'` means `w'` is now-or-later than `w`. -/
  T : W → W → Prop
  /-- `R` is transitive (validates the `4` axiom). -/
  R_trans : Transitive R
  /-- `R` is converse well-founded (validates Löb's axiom; encodes "no infinite proofs"). -/
  R_wf : WellFounded (fun a b => R b a)
  /-- Time is reflexive. -/
  T_refl : Reflexive T
  /-- Time is transitive. -/
  T_trans : Transitive T
  /-- Provability is monotone in time: future successors are present successors. -/
  compat : ∀ {w w' v : W}, T w w' → R w' v → R w v

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

/-- A concrete two-world temporal GL frame: today (`true`) sees one counterexample
world (`false`), tomorrow (`false`) sees none. It satisfies every frame axiom,
including time-monotonicity. -/
def boolTempFrame : TempFrame where
  W := Bool
  R := fun a b => a = true ∧ b = false
  T := fun a b => a = b ∨ (a = true ∧ b = false)
  R_trans := by intro a b c hab hbc; revert a b c; decide
  R_wf := by
    have : IsTrans Bool (fun a b => b = true ∧ a = false) :=
      ⟨by intro a b c; revert a b c; decide⟩
    have : Std.Irrefl (fun a b : Bool => b = true ∧ a = false) :=
      ⟨by intro a; revert a; decide⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  T_refl := by intro a; revert a; decide
  T_trans := by intro a b c; revert a b c; decide
  compat := by intro w w' v; revert w w' v; decide

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

/-- A **time-stamped provability predicate** `prov t A` ("a proof of `A` is established
by stage `t`"), axiomatised abstractly. This is the arithmetical target: `prov` models
`∃ proof of `A` of size ≤ `t`` over Peano Arithmetic. -/
structure TempProv where
  /-- `prov t A` : `A` is provably established by time `t`. -/
  prov : ℕ → Prop → Prop
  /-- Persistence: an established proof stays established. -/
  persist : ∀ {t s : ℕ} {A : Prop}, t ≤ s → prov t A → prov s A
  /-- Internal modus ponens at each time. -/
  K : ∀ {t : ℕ} {A B : Prop}, prov t (A → B) → prov t A → prov t B
  /-- Σ₁-completeness / positive introspection: established proofs are self-certifying. -/
  sigma1 : ∀ {t : ℕ} {A : Prop}, prov t A → prov t (prov t A)
  /-- Löb's rule at each time. -/
  loeb : ∀ {t : ℕ} {A : Prop}, prov t (prov t A → A) → prov t A

-- !-- Time-stamped Gödel II: `¬ prov t False` is `prov t False → False`, so
--     `prov t (¬ prov t False)` is `prov t (prov t False → False)`; Löb (at `A = False`)
--     turns this into `prov t False`, contradicting consistency. -- !--

-- !-- Combine Σ₁-completeness (`prov t A → prov t (prov t A)`) with persistence
--     (`t ≤ s`) to push the certificate forward in time. -- !--

-- !-- Restatement of the `persist` field: provability is monotone in time. -- !--

/-- The degenerate "proves nothing" model of the time-stamped provability axioms.
It witnesses that the `TempProv` axioms are mutually consistent, so the Gödel results
above are not vacuous. (Arithmetically faithful — non-degenerate — models are the
content of the arithmetical-completeness conjecture in `FUTURE_DIRECTIONS.md`.) -/
def trivialTempProv : TempProv where
  prov := fun _ _ => False
  persist := fun _ h => h
  K := fun h _ => h
  sigma1 := fun h => h
  loeb := fun h => h


/-! ## Part 5 — Boundary: why converse well-foundedness is essential -/

-- !-- One reflexive world `()` with `R = ⊤`. Then `□A → A` collapses to `A → A` (true),
--     so `□(□A→A)` holds, yet `□A = A = False` fails: Löb's axiom is invalid once the
--     converse-well-foundedness of `TempFrame.R_wf` is dropped. -- !--

end TemporalGL


