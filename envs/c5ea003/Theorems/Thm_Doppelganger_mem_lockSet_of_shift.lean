-- Prove2me | Theorems.Thm_Doppelganger_mem_lockSet_of_shift
-- name    : Doppelganger.mem_lockSet_of_shift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:42:10.593917+00:00
-- url     : https://prove2.me/theorems/d0dcaf45-af18-4ec1-8c9d-bac3e3120558
-- title:
--   Locking a stream is inherited from its shift: if the doppelgängers lock along the
-- statement:
--   Locking a stream is inherited from its shift: if the doppelgängers lock along the
--   stream from which the first stimulus has been deleted, they lock along the stream.
--
--   ```lean
--   theorem Doppelganger.mem_lockSet_of_shift(δ : S → I → S) (x : ℕ → I)
--       (h : (fun k => x (k + 1)) ∈ LockSet δ) : x ∈ LockSet δ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Topology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Topology.lean#L68

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

theorem Doppelganger.mem_lockSet_of_shift(δ : S → I → S) (x : ℕ → I)
    (h : (fun k => x (k + 1)) ∈ LockSet δ) : x ∈ LockSet δ := by sorry
