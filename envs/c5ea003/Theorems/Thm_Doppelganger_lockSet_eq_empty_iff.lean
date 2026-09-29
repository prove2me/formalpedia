-- Prove2me | Theorems.Thm_Doppelganger_lockSet_eq_empty_iff
-- name    : Doppelganger.lockSet_eq_empty_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:42:00.560621+00:00
-- url     : https://prove2.me/theorems/5775b14f-b3d4-467b-9754-7ebbde2f466c
-- title:
--   The lock set is empty exactly for non-locking agents.
-- statement:
--   The lock set is empty exactly for non-locking agents.
--
--   ```lean
--   theorem Doppelganger.lockSet_eq_empty_iff[Nonempty I] (δ : S → I → S) :
--       LockSet δ = ∅ ↔ ¬ PhaseLocking δ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Topology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Topology.lean#L124

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Topology.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
/-
# Doppelgänger Phase-Lock — the topology of locking stimulus streams

Real environments do not hand the agents a finite word; they hand them an infinite
stimulus stream `x : ℕ → I`.  Equip the stream space with the product topology of the
discrete stimulus alphabet (the Cantor topology).  The **lock set**

`LockSet δ = {x | some finite prefix of x phase-locks the two agents}`

is then a topological object, and this file determines its topological type exactly:

* it is always **open** — locking is a finitary, observable event: it is decided by a
  finite prefix, so it survives every sufficiently small perturbation of the stream;
* it is **dense** as soon as the agent is phase-locking at all — any experiment, no matter
  how it has been constrained on finitely many observations, can still be continued into a
  locking stream;
* consequently it is either **empty** (non-locking agent) or **open and dense**, with
  nowhere-dense complement: a topological zero–one law for doppelgänger telepathy.

## Main results

* `Doppelganger.isOpen_lockSet`
* `Doppelganger.dense_lockSet`
* `Doppelganger.lockSet_eq_empty_iff`
* `Doppelganger.lockSet_dichotomy` — the zero–one law.
* `Doppelganger.interior_compl_lockSet` — nowhere-density of the failure set.
-/

open Doppelganger

variable {S I : Type*}








variable [TopologicalSpace I] [DiscreteTopology I]



omit [TopologicalSpace I] [DiscreteTopology I] in

theorem Doppelganger.lockSet_eq_empty_iff[Nonempty I] (δ : S → I → S) :
    LockSet δ = ∅ ↔ ¬ PhaseLocking δ := by sorry
