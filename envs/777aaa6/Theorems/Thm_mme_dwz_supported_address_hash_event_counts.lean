-- Prove2me | Theorems.Thm_mme_dwz_supported_address_hash_event_counts
-- name    : mme_dwz_supported_address_hash_event_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:02:01.599988+00:00
-- url     : https://prove2.me/theorems/28ab0112-904a-4001-bd44-dd635ed739a0
-- title:
--   Exact affine hash-event counts for supported natural coarse addresses
-- statement:
--   Let $p$ be an odd prime, let $d<p$ be a nonnegative integer, and let
--   $S\subseteq\{0,\ldots,p-1\}$. Fix a bijection between $N$ positions and
--   $H+1$ hash coordinates. Let $\mathcal A$ be a finite indexed family of distinct
--   coarse addresses
--   $a=(I_a,J_a,K_a)\in(\mathbb N^N)^3$ satisfying
--   $I_a(t)+J_a(t)+K_a(t)=d$ at every position.
--
--   On the actual affine hash-state space
--   $$
--   \Omega=(\mathbb F_p^{H+2})\times\mathbb F_p,
--   $$
--   define $E_a$ to be the set of states for which the X, Y, and Z hashes of
--   address $a$ all equal one common element of $S$, reduced modulo $p$.
--   Then
--   $$
--   |\Omega|=p^{H+3},\qquad |E_a|=|S|p^{H+1}\quad(a\in\mathcal A).
--   $$
--   For distinct $a,b\in\mathcal A$ sharing any one of their X, Y, or Z address
--   words,
--   $$
--   |E_a\cap E_b|\le |S|p^H.
--   $$
--
--   The event sets are constructed from the literal natural-address retention
--   predicate; they are not additional data with assumed counts. Thus the finite
--   DWZ extraction theorem may take $K_0=|S|p^{H+1}$ and
--   $J_0=|S|p^H$, with $K_0=pJ_0$. The condition $d<p$ prevents distinct natural
--   coarse grades from becoming equal modulo $p$. The index-to-address map need
--   only be injective on $\mathcal A$. Empty label sets and empty ambient families
--   are allowed. No progression-freeness, marginal condition, star-degree bound,
--   or compatible-subfiber cardinality estimate is asserted or required here.
-- source:
--   Derived finite-cardinality bridge for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.10 (the displayed affine hashes and Lemma 3.11), Section 6.1 Step 3, and Section 6.2 Claim 6.8. https://arxiv.org/html/2210.10173v5#S3.SS10 . This exact natural-address formulation supplies the single and shared-X/Y/Z event inputs to the finite extraction theorem. The explicit level<p and ambient address injectivity hypotheses prevent modular aliasing and duplicated coarse addresses; it does not establish isolation or compatible-degree estimates.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

open MME MME.DWZSimultaneous BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem mme_dwz_supported_address_hash_event_counts
    (N H level p R : ℕ) [Fact p.Prime] (hpodd : Odd p) (hlevel : level < p)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hS : S ⊆ Finset.range p)
    (address : Fin R → CoarseAddress N) (ambient : Finset (Fin R))
    (hsupport : ∀ a ∈ ambient, Supported level (address a))
    (hinjective : Set.InjOn address (ambient : Set (Fin R))) :
    let events := fun a ↦ Finset.univ.filter
      (fun state : (Fin (H + 2) → ZMod p) × ZMod p ↦
        Retained level reindex S state (address a))
    (∀ a state, state ∈ events a ↔ Retained level reindex S state (address a)) ∧
    Fintype.card ((Fin (H + 2) → ZMod p) × ZMod p) = p ^ (H + 3) ∧
    (∀ a ∈ ambient, (events a).card = S.card * p ^ (H + 1)) ∧
    (∀ a ∈ ambient, ∀ b ∈ ambient, a ≠ b →
      (∃ i : Fin 3, address a i = address b i) →
      (events a ∩ events b).card ≤ S.card * p ^ H) := by sorry
