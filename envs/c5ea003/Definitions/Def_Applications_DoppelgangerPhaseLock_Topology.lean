-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
-- name    : Applications_DoppelgangerPhaseLock_Topology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:23.699427+00:00
-- url     : https://prove2.me/theorems/decc1b69-86dd-4dfa-9bd9-721ac1f07c57
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Topology
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Topology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Topology.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
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

namespace Doppelganger

variable {S I : Type*}

/-- The set of infinite stimulus streams that phase-lock the doppelgänger pair after
finitely many observations. -/
def LockSet (δ : S → I → S) : Set (ℕ → I) := {x | ∃ n, Locks δ (pre x n)}

/-- Splice: follow the stream `x` for `N` observations, then observe the word `w`
(and the filler stimulus `c` afterwards). -/
def splice (x : ℕ → I) (N : ℕ) (w : List I) (c : I) : ℕ → I :=
  fun k => if k < N then x k else w.getD (k - N) c





section Topology

variable [TopologicalSpace I] [DiscreteTopology I]






end Topology

end Doppelganger


