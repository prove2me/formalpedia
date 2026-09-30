-- Prove2me | Theorems.Thm_Hirsch_moment_odd_catalogue_stellar_bound
-- name    : Hirsch.moment_odd_catalogue_stellar_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T03:43:19.582211+00:00
-- url     : https://prove2.me/theorems/66949890-ea3b-473d-8ea4-6fb6c863d364
-- title:
--   The concrete odd moment catalogue forces a binomial stellar flag-completion bound
-- statement:
--   For the original 2k-dimensional mean-centered moment inequalities on natural labels 0,...,4k, define the initial face family by actual feasible tight-row intersections. For any finite sequence of t actual forward stellar subdivisions with finite supports, fresh vertices and faces of size at least two, if every final minimal nonface has cardinality two, prove choose(2k,k+1)+t <= choose(4k+1+t,2). The proof constructs all (k+1)-subsets of the 2k odd labels, proves their minimal incompatibility via constructed sorted interleaved pairs, proves the catalogue map injective and its exact binomial cardinality, then applies the accepted finite stellar persistence theorem. No supplied catalogue, separators, incompatibility, cardinality growth or binomial-count hypothesis is used. This is a full catalogue/count assembly for the explicit original-row system, not a universal original-edge diameter bound or a separately formalized polytopal realization/asymptotic theorem.
-- source:
--   Continues accepted #281, #285, #286, #287 and #288 in jjoshua2/prove2me-work. Reuses the actual accepted namespace proof bodies rather than assuming their conclusions. Mathlib Finset.orderEmbOfFin constructs the sorted enumeration; powersetCard counts the explicit family. Classical moment geometry is credited; no historical-priority claim.

import Mathlib

open scoped BigOperators

namespace Hirsch
theorem moment_odd_catalogue_stellar_bound (k t : ℕ)
    (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ)
    (hV0 : V 0 = Finset.range (4*k+1))
    (hK0 : K 0 = {N | N ⊆ Finset.range (4*k+1) ∧ ∃ x : Fin (2*k) → ℝ,
      (∀ i : Fin (4*k+1),
        (∑ j : Fin (2*k), ((i.val : ℝ) ^ (j.val+1) -
          (∑ l : Fin (4*k+1), (l.val : ℝ) ^ (j.val+1)) / ((4*k+1 : ℕ) : ℝ)) * x j) ≤ 1) ∧
      ∀ n ∈ N,
        (∑ j : Fin (2*k), ((n : ℝ) ^ (j.val+1) -
          (∑ l : Fin (4*k+1), (l.val : ℝ) ^ (j.val+1)) / ((4*k+1 : ℕ) : ℝ)) * x j) = 1})
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) =
      {T | if z i ∈ T then
        (T.erase (z i) ∪ E i) ∈ K i ∧ ¬ E i ⊆ T.erase (z i)
        else T ∈ K i ∧ ¬ E i ⊆ T})
    (hflag : ∀ N : Finset ℕ, N ⊆ V t →
      (N ∉ K t ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K t) → N.card = 2) :
    (2*k).choose (k+1) + t ≤ (4*k+1+t).choose 2 := by sorry
end Hirsch
