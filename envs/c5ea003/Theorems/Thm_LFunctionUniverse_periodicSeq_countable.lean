-- Prove2me | Theorems.Thm_LFunctionUniverse_periodicSeq_countable
-- name    : LFunctionUniverse.periodicSeq_countable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:08.029988+00:00
-- url     : https://prove2.me/theorems/f55af9e3-4b79-43bb-8e8b-ad85b7b1cbc5
-- title:
--   Periodic sequences over a countable alphabet form a countable set.
-- statement:
--   **Periodic sequences over a countable alphabet form a countable set.**
--
--   A periodic sequence is determined by its period `n` and the finite block of values
--   `Fin n → V`; there are only countably many such finite data, so only countably many
--   periodic sequences.  This is the mechanism by which the arithmetic constraint of
--   periodicity collapses an *a priori* continuum-sized family of Dirichlet series to a
--   countable one.
--
--   ```lean
--   theorem LFunctionUniverse.periodicSeq_countable{V : Type*} [Countable V] :
--       {a : ℕ → V | IsPeriodicSeq a}.Countable := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/LFunctionUniverse/PeriodicUniverse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/LFunctionUniverse/PeriodicUniverse.lean#L33

-- Thm stub generated from Applications/LFunctionUniverse/PeriodicUniverse.lean
import Mathlib
import Definitions.Def_Applications_LFunctionUniverse_PeriodicUniverse

/-!
# The L-function universe, part II: the periodic/arithmetic universe is countable

The Dirichlet L-functions — the L-functions attached to Dirichlet characters — have
coefficient sequences `a(k) = χ(k)` that are **periodic** (period dividing the
conductor) and take values in a **countable** set (roots of unity, together with
`0`).  This is the arithmetic constraint that tames the otherwise uncountable
universe of Dirichlet series studied in `NaiveUniverse.lean`.

The main abstract result of this file is:

* `periodicSeq_countable`: for any *countable* value type `V`, the set of periodic
  sequences `ℕ → V` is countable.

The intuition ("a periodic sequence is determined by a finite block of data") is
made precise via the surjection sending the finite data `(period, one full block of
values)` to the corresponding periodic sequence.

We then apply the countable-value idea to the genuine number-theoretic object: the
family of all Dirichlet characters (over all moduli) is countable, so there are only
countably many Dirichlet L-functions.
-/

open scoped Classical

open LFunctionUniverse

theorem LFunctionUniverse.periodicSeq_countable{V : Type*} [Countable V] :
    {a : ℕ → V | IsPeriodicSeq a}.Countable := by sorry
