-- Prove2me | Definitions.Def_Probability_TalagrandLIS
-- name    : Probability_TalagrandLIS
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:03.048044+00:00
-- url     : https://prove2.me/theorems/92d2b287-6de7-4aee-b191-e2fd75a03d80
-- title:
--   Aether Catalog definitions — Probability_TalagrandLIS
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandLIS`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandLIS.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TalagrandCertifiable

/-!
# Concentration of the longest increasing subsequence

The classical application of Talagrand's inequality that bounded differences
cannot reach: the length `L` of the longest (weakly) increasing subsequence of a
random word concentrates on the scale `√L` rather than `√m`, because a witnessing
subsequence is a *certificate* of size `L` in the sense of
`Talagrand.certifiable_concentration`.

## Main results

* `Talagrand.lis` — the length of the longest increasing subsequence of a word
  `x : Fin m → α` over a linearly ordered alphabet, as a real number.
* `Talagrand.lis_lipschitz` — `lis` is `1`-Lipschitz for the plain Hamming metric.
* `Talagrand.lis_cert` — a witnessing subsequence of length `⌈l⌉` certifies
  `lis ≥ l`.
* `Talagrand.lis_concentration` — for an arbitrary product measure on words,
  `P(lis ≤ b) · P(lis ≥ l) ≤ exp (-(l - b)² / (4⌈l⌉))`.  The deviation scale is
  `√l`, not `√m`.
-/

namespace Talagrand

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] {m : ℕ}

/-- `S` indexes a weakly increasing subsequence of the word `x`. -/
def IsIncr (x : Fin m → α) (S : Finset (Fin m)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≤ j → x i ≤ x j

instance (x : Fin m → α) : DecidablePred (IsIncr x) := fun _ => by
  unfold IsIncr; infer_instance

/-- The length of the longest weakly increasing subsequence of `x`. -/
def lis (x : Fin m → α) : ℝ :=
  (((Finset.univ.filter (IsIncr x)).sup Finset.card : ℕ) : ℝ)










end Talagrand


