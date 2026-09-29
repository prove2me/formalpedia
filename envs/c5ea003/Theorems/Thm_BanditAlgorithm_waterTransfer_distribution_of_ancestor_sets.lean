-- Prove2me | Theorems.Thm_BanditAlgorithm_waterTransfer_distribution_of_ancestor_sets
-- name    : BanditAlgorithm.waterTransfer_distribution_of_ancestor_sets
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:45:18.694531+00:00
-- url     : https://prove2.me/theorems/523ffb1a-f133-45b6-ac8a-b3737e08f819
-- title:
--   Water-transfer distribution from finite ancestor sets
-- statement:
--   Let q be a probability distribution on k>0 vertices. For every vertex b, let anc(b) be a nonempty set of ancestors containing b itself. Let R(a,b) be a relation such that whenever R(a,b) holds, every ancestor set containing b also contains a. Then there is a probability distribution r with three properties:
--
--   $$
--   r_a\geq q_a/k,
--   $$
--
--   r is monotone along R, and for every potential y that is nondecreasing from each vertex toward all of its ancestors,
--
--   $$
--   \sum_b q_b y_b\leq\sum_a r_a y_a.
--   $$
--
--   The construction is explicit: each mass q_b is split uniformly among anc(b). This is the abstract counting core of the water-transfer operator in Lemma 37.20 and is reusable independently of partial monitoring.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Lemma 37.20, printed pp. 500--501, https://tor-lattimore.com/downloads/book/book.pdf

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace BanditAlgorithm

/-! Abstract finite form of the construction in Lattimore--Szepesvári,
Lemma 37.20, printed pp. 500--501. -/

theorem waterTransfer_distribution_of_ancestor_sets
    {k : ℕ} (hk : 0 < k) (q : Fin k → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin k))
    (anc : Fin k → Finset (Fin k))
    (hself : ∀ b, b ∈ anc b)
    (R : Fin k → Fin k → Prop)
    (hclosure : ∀ a b, R a b → ∀ c, b ∈ anc c → a ∈ anc c) :
    ∃ r : Fin k → ℝ,
      r ∈ stdSimplex ℝ (Fin k) ∧
      (∀ a, q a / k ≤ r a) ∧
      (∀ a b, R a b → r b ≤ r a) ∧
      ∀ y : Fin k → ℝ,
        (∀ a b, a ∈ anc b → y b ≤ y a) →
          ∑ b : Fin k, q b * y b ≤ ∑ a : Fin k, r a * y a := by
  sorry

end BanditAlgorithm
