-- Prove2me | Definitions.Def_Logic_PosetTheory_StronglyCriticalOrdinals
-- name    : Logic_PosetTheory_StronglyCriticalOrdinals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:29.839547+00:00
-- url     : https://prove2.me/theorems/be3585d9-6fd4-48b3-a1c1-affff80ea4bf
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_StronglyCriticalOrdinals
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.StronglyCriticalOrdinals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/StronglyCriticalOrdinals.lean by skeleton subtraction
import Mathlib

/-!
# Strongly critical ordinals and predicative ordinal analysis

This file develops a self-contained fragment of *predicative ordinal analysis* on top of
Mathlib's Veblen hierarchy (`Ordinal.veblen`, `Ordinal.epsilon`, `Ordinal.gamma`).

The organizing concept is the **strongly critical ordinal**: a positive ordinal that is a
fixed point of the *unary* Veblen function `veblen · 0`.  The decisive structural fact is
that this single fixed-point condition automatically upgrades to closure under the *full
binary* Veblen function (`StronglyCritical.veblen_lt`), generalizing the classical
Feferman–Schütte statement (usually phrased only for `Γ₀`) to arbitrary strongly critical
ordinals.

We then separate the *arithmetic* of the Veblen tower from the *order theory* of system
strength: by recognizing the consistency-strength relation as an `InvImage` of `<` on
`Ordinal`, well-foundedness of ordinal analysis and the impossibility of infinite
consistency descent both descend from `Ordinal.lt_wf`.

## Main results

* `StronglyCritical.veblen_eq` — a strongly critical `o` is a common fixed point of every
  lower Veblen function.
* `StronglyCritical.veblen_lt` (flagship) — predicative closure under the full binary
  Veblen function for *any* strongly critical ordinal.
* `gamma_stronglyCritical`, `gamma_zero_stronglyCritical` — every `Γ_ β`, and in particular
  the Feferman–Schütte ordinal `Γ₀`, is strongly critical.
* `gamma_zero_least_stronglyCritical` — `Γ₀` is the least strongly critical ordinal.
* `epsilon_zero_not_stronglyCritical` — `ε₀` is *not* strongly critical, so the closure
  bound `Γ₀` is sharp.
* `predicative_tower` — the landmark chain `ω < ε₀ < Γ₀`.
* `strength_wellFounded`, `no_infinite_consistency_descent` — order-theoretic consequences
  of `Ordinal.lt_wf` for proof-theoretic strength.
-/

namespace Predicative

open Ordinal Set

/-- A **strongly critical** ordinal is a positive fixed point of the unary Veblen function
`veblen · 0`.  Equivalently (see `mem_range_gamma`) it is a value of Mathlib's `gamma`. -/
def StronglyCritical (o : Ordinal) : Prop := 0 < o ∧ veblen o 0 = o

-- !-- `Γ_ β` is positive (`gamma_pos`) and a Veblen fixed point (`veblen_gamma_zero`). -- !--

-- !-- Specialize `gamma_stronglyCritical` at `β = 0`, where `Γ_ 0 = Γ₀`. -- !--

-- !-- From `veblen o 0 = o` and `veblen_veblen_of_lt` (with `b = 0`), every lower Veblen
-- function fixes `o`. -- !--

-- !-- With `veblen a o = o` and right strict monotonicity, `b < o` gives
-- `veblen a b < veblen a o = o`. -- !--

-- !-- Specialization of the flagship to `Γ₀`, which is strongly critical
-- (`gamma_zero_stronglyCritical`). -- !--

-- !-- `veblen o 0 = o ≤ o` feeds `gamma_zero_le_of_veblen_le`. -- !--

-- !-- If `ε₀` were strongly critical then `Γ₀ ≤ ε₀`, contradicting `ε₀ < Γ_ 0 = Γ₀`. -- !--

-- !-- Assemble `omega0_lt_epsilon`, `epsilon_zero_lt_gamma`, the boundary probe, and
-- `gamma_zero_stronglyCritical`. -- !--

/-! ### Order theory of consistency strength

We model a formal system *analyzed by ordinal analysis* by the single datum of its
proof-theoretic ordinal, and show that comparing strength by this ordinal is well-founded.
-/

/-- A formal system equipped with its proof-theoretic ordinal (its *proof-theoretic
ordinal*, `pto`).  Strength is compared via this ordinal. -/
structure OrdAnalyzedSystem where
  /-- The proof-theoretic ordinal assigned to the system by ordinal analysis. -/
  pto : Ordinal


-- !-- The strength relation is the `InvImage` of `<` on `Ordinal` under `pto`, so
-- `InvImage.wf` applied to `Ordinal.lt_wf` finishes. -- !--

-- !-- A strictly descending sequence of `pto`s yields `RelEmbedding.natGT` into `Ordinal`,
-- contradicting `Ordinal.lt_wf` via `RelEmbedding.not_wellFounded`. -- !--

end Predicative


