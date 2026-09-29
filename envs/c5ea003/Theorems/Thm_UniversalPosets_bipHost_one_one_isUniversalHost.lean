-- Prove2me | Theorems.Thm_UniversalPosets_bipHost_one_one_isUniversalHost
-- name    : UniversalPosets.bipHost_one_one_isUniversalHost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:06:02.750825+00:00
-- url     : https://prove2.me/theorems/9725aec7-9d21-4bc0-a254-555f4eb2c512
-- title:
--   The three-point host `BipHost 1 1` (a two-element chain together with an
-- statement:
--   The three-point host `BipHost 1 1` (a two-element chain together with an
--   isolated point) contains **every** partial order on two points as an induced
--   subposet.
--
--   ```lean
--   theorem UniversalPosets.bipHost_one_one_isUniversalHost: IsUniversalHost (BipHost 1 1) (Fin 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/SmallCases.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/SmallCases.lean#L90

-- Thm stub generated from Cryptography/UniversalPosets/SmallCases.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds

/-!
# Exact small cases: the counting bound is not tight

`Bounds.lean` proves `2 ^ m ≤ N ^ 2` for every host of the `(m,m)`-bipartite
posets and exhibits a host of size `m·2^m + m`.  Here the smallest case
`m = 1` (that is, `n = 2` points) is settled *exactly*: the optimal host has
`3` points, while the counting bound only gives `2`.  So the counting lower
bound is already lossy at `n = 2`, which is the finite shadow of the
`n/4` versus `n/2` gap discussed in the motivating paper.

-- !-- Lab Notes -- !--
Experiment (Experimenter).  All `19` partial orders on `3` points and all `3`
partial orders on `2` points were enumerated (see `ComputationalEvidence.md`).
For `n = 2` the three orders are the antichain and the two chains; a host must
contain a comparable pair and an incomparable pair, and a two-element poset is
either a chain or an antichain -- never both.  Hence `N ≥ 3`, and the explicit
host `BipHost 1 1` (a two-chain plus an isolated point) attains it.

Analysis (Analyst).  The obstruction is *reuse*: the counting argument allows a
host of `N` points to serve `N^n` embeddings, but comparability constraints
between host points cannot be switched off.  This is exactly the loss that the
regularity method of the paper repairs asymptotically.

Critique (Critic).  The lower bound `3 ≤ N` is proved for arbitrary finite
partially ordered hosts, not just for the constructed one, and the matching
construction is explicit; the statement is therefore sharp and non-vacuous.
-/

open UniversalPosets

theorem UniversalPosets.bipHost_one_one_isUniversalHost: IsUniversalHost (BipHost 1 1) (Fin 2) := by sorry
