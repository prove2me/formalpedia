-- Prove2me | Theorems.Thm_Hirsch_stellar_persistence_count
-- name    : Hirsch.stellar_persistence_count
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T21:54:50.454442+00:00
-- url     : https://prove2.me/theorems/5d525d51-5d42-4dac-a3dd-91ea83902e77
-- title:
--   Certified minimal nonfaces persist through stellar sequences and bound flag completion size
-- statement:
--   For any finite sequence of t forward stellar subdivisions of downward-closed finite set systems supported on vertex sets V(i), each at an actual face of size at least two with a fresh vertex, any finite certified subfamily A of the initial inclusion-minimal nonfaces satisfies |A|+t <= binom(|V(0)|+t,2) if every final inclusion-minimal nonface has size two. The actual stellar membership rule is an explicit hypothesis, not an abstract monotonicity oracle. The proof derives canonical distinct descendants, a new nonface at every step, their support and exact cardinality, and then the final pair count. Completeness of A is not assumed. This is the finite combinatorial counting core of the project's forward-stellar flagification obstruction, not a claim of a polytope diameter lower bound or a solution to Polynomial Hirsch.
-- source:
--   Formalizes the finite persistence/counting core of jjoshua2/prove2me-work PR #267, research/STELLAR_NONFACE_PERSISTENCE.md. The proof is direct finite set reasoning and imports only Mathlib. Stellar subdivision background: Lutz and Nevo, Stellar theory for flag complexes, arXiv:1302.5197. No claim of historical priority. The cyclic-polytope exponential family, graph diameter consequences, arbitrary non-stellar subdivisions, and inverse operations are not part of this formal statement.

import Mathlib

namespace Hirsch
theorem stellar_persistence_count
    (t : ℕ) (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ) (A : Finset (Finset ℕ))
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
    (hA : ∀ N ∈ A, N ⊆ V 0 ∧
      N ∉ K 0 ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K 0)
    (hflag : ∀ N : Finset ℕ, N ⊆ V t →
      (N ∉ K t ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K t) → N.card = 2) :
    A.card + t ≤ ((V 0).card + t).choose 2 := by sorry
end Hirsch
