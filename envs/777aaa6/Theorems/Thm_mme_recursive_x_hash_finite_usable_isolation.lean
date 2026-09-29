-- Prove2me | Theorems.Thm_mme_recursive_x_hash_finite_usable_isolation
-- name    : mme_recursive_x_hash_finite_usable_isolation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T08:58:38.644022+00:00
-- url     : https://prove2.me/theorems/d6e9bda5-7549-4097-8360-44835665e2b7
-- title:
--   Recursive hashing: simultaneous usable-copy selection
-- statement:
--   Fix finite words of admissible left-half splits, with an exact joint-count target family $T$ inside the family $A$ having the prescribed three marginal counts. Let $N_X$ be the number of distinct $X$ blocks of $A$. Use the physical asymmetric affine hashes over an odd prime field of order $p$, where the grades are smaller than $p$, and use a three-term-progression-free label set $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$.
--
--   For each hash state $q$, prescribe an arbitrary finite family $G_q$ of usable triples; usability may depend on that same state. Suppose $8|A|\le pN_X$ and
--
--   $$\sum_q |T\cap E_q\cap G_q|\ge \frac78 |T||S|p^{N+1},$$
--
--   where $E_q$ is the ambient family surviving the three coordinate-bucket filters. Then there are a state $q$ and a family $I\subseteq T\cap E_q\cap G_q$ such that every $X$ block of $I$ occurs in exactly its own triple throughout $E_q$, and
--
--   $$|I|\ge\frac{|T||S|}{2p^2}.$$
--
--   This lemma allows the Y/Z usability losses and the X collision losses to be controlled in a single state-selection argument. The usable-incidence estimate is a hypothesis; it is not claimed here for the concrete More Asymmetry profiles.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.2 and 6.5, Claims 6.6 and 6.21; https://arxiv.org/html/2404.16349v2#S6.SS2. This is an explicit finite auxiliary lemma for the source argument, not a verbatim restatement of an asymptotic claim.

import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
import Theorems.Thm_mme_finset_weighted_collision_averaging_isolated
import Theorems.Thm_mme_dwz_target_two_mode_collision_card_le_of_degree
import Theorems.Thm_mme_dwz_asymmetric_hash_exact_incidence_sums
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
set_option autoImplicit false

theorem mme_recursive_x_hash_finite_usable_isolation (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    {N p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hgrade : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) (hSfree : ThreeAPFree (S : Set ℕ))
    (hbudget : 8 * (ambient (n := n) m).card ≤
      p * ((ambient (n := n) m).image (block 0)).card)
    (good : ((Fin (N + 2) → ZMod p) × ZMod p) → Finset (Address half R parent n))
    (hgood : (7 / 8 : ℝ) * ((target (n := n) m).card * S.card * (p : ℝ) ^ (N + 1)) ≤
      ∑ q, ((((target m).filter (fun a ↦
        a ∈ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q)) ∩ good q).card : ℝ)) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
      I ⊆ target m ∧
      I ⊆ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
      I ⊆ good q ∧
      (∀ a ∈ I, ∀ b ∈ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q,
        block 0 a = block 0 b → a = b) ∧
      ((target (n := n) m).card : ℝ) * S.card / (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by sorry
