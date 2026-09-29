-- Prove2me | Theorems.Thm_mme_CW_2376_hash_budget_of_degree
-- name    : mme_CW_2376_hash_budget_of_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:38:40.766999+00:00
-- url     : https://prove2.me/theorems/5f57a844-3563-45b0-a1e1-09e471f6030f
-- title:
--   A normalized degree margin yields the full CW target-surplus hash state
-- statement:
--   Let $Dstar$ be the exact target completion degree and suppose the target count factors as $T=V Dstar$. Let $D$ uniformly bound every full marginal-supported completion star in each mode. If the normalized prime-field margin pays a reserve term and all three directed collision budgets, then there is a retained full marginal hypergraph $E$ that is vertex-closed and satisfies $|C(T(E),E)|+V$ times the reserve loss at most $|T(E)|$.
--
--   The proof reinserts the common hash-fiber factors, applies the $3TD$ collision-universe bound, and invokes deterministic averaging over all augmented affine states. It isolates all probabilistic incidence bookkeeping from the remaining profile-completion count and prime/Behrend choice.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), completion degrees, affine hashing, and collision deletion on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_CW_2376_hash_budget_select
import Theorems.Thm_mme_CW_2376_collision_universe_card_of_degree
import Theorems.Thm_mme_CW_2376_aggregate_budget_of_normalized_margin

open MME

set_option autoImplicit false

theorem mme_CW_2376_hash_budget_of_degree
    (m p D Dstar : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (V loss : ℝ) (hV : 0 ≤ V)
    (hT : ((cw2376AllExactTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ))
    (hdeg : ∀ i : Fin 3, ∀ a ∈ cw2376AllExactTargetEdges m,
      ((cw2376MarginalSupportedUniverse m).filter
        (fun b => b.1 i = a.1 i)).card ≤ D)
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ)) :
    ∃ E : Finset (CW2376MarginalSupportedAddress m),
      CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) + V * loss ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  sorry
