-- Prove2me | Theorems.Thm_Hirsch_protected_facet_state_count
-- name    : Hirsch.protected_facet_state_count
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T23:47:30.579905+00:00
-- url     : https://prove2.me/theorems/37330e52-f970-45f1-9d48-d53617ec7c9a
-- title:
--   Protected-facet intervals bound the number of visited uniform states
-- statement:
--   For a finite injective sequence P of n distinct d-element subsets of a finite ground set V, suppose every label outside a specified finite exception set B occurs during at most one interval of the sequence. Then n <= (|V|-d+1)*2^|B|. More precisely, for any finite collection C covering all exceptional signatures P(i) intersect B, n <= (|V|-d+1)*|C| and n <= sum over S in C of (|V minus B| - (d-|S|)+1), with natural-number truncated subtraction. The proof constructs the encoding (current exceptional signature, count of previously seen protected labels no longer active) and proves it injective. No bound on visits per signature is an assumption. No adjacency, geometric realization, small exception-set existence, flagness, or polynomial diameter is assumed or concluded. This is the positive finite counting core of the project's conditional facet-confinement route bound.
-- source:
--   Formalizes and sharpens the proof interface of jjoshua2/prove2me-work PR #259, research/DEFECT_CONFINEMENT.md. Direct finite-set counting with a new explicit signature/retirement injection; no historical-priority claim. The separate geometric implication from missing-link-triangle confinement to protected intervals and the universal Polynomial Hirsch conjecture are outside this statement.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem protected_facet_state_count
    (n d : ℕ) (V B : Finset ℕ) (P : Fin n → Finset ℕ)
    (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d)
    (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j) :
    n ≤ (V.card - d + 1) * 2 ^ B.card ∧
      ∀ C : Finset (Finset ℕ), (∀ i, P i ∩ B ∈ C) →
        n ≤ (V.card - d + 1) * C.card ∧
          n ≤ ∑ S ∈ C, ((V \ B).card - (d - S.card) + 1) := by sorry
end Hirsch
