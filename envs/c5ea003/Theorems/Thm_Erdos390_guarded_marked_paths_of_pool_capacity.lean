-- Prove2me | Theorems.Thm_Erdos390_guarded_marked_paths_of_pool_capacity
-- name    : Erdos390.guarded_marked_paths_of_pool_capacity
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T16:59:52.230022+00:00
-- url     : https://prove2.me/theorems/b4fa271b-7061-4f4a-a796-d25e075a16e6
-- title:
--   Construct guarded marked paths from finite pool capacities
-- statement:
--   Fix the lengths, positive integer cores, common edge scales, and cofactor bound of a family of signed prime-to-one paths. Assign each component request to a pool of available prime markers. Assume distinct pools are disjoint and every pool contains at least as many markers as requests assigned to it:
--   $$\#\{r:\operatorname{pool}(r)=j\}\le\#A_j.$$
--   Every available marker exceeds the common cofactor bound. For each request, every marker in its pool makes both endpoint factors legal and avoids a specified forbidden set.
--
--   Then there exists a marked-path datum with the given lengths, cores, scales and cofactor bound. Its markers are globally distinct, and both states of every signed slot lie in the legal ambient set and avoid the forbidden set.
--
--   This is the finite construction step behind the source's disjoint donor assignment: pool capacities yield actual injections, which combine because the numerical pools are disjoint. Analytic prime supply and compatibility with the charged fractional certificate are not asserted here.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 5, Lemma bank-donor-injection and equations bank-ordinary-congestion, bank-bottom-congestion. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . Finite embedding argument in BankOrdinaryPoolMatching.lean, section Finite poolwise matching, and BankBottomPoolMatching.lean, exists_bankBottomPool_injective_assignment. Here the generic matching is applied to the previously formalized prime-marked path interface; numerical capacity estimates remain explicit hypotheses.

import Definitions.Def_erdos390_marked_bank_paths
open Erdos390.WholePaper

theorem Erdos390.guarded_marked_paths_of_pool_capacity
    {Pool : Type*} [DecidableEq Pool]
    (P : Finset ℕ) (β : ↑P → ℕ)
    (steps : SignedBankSlot β → ℕ)
    (core : SignedBankSlot β → ℕ → ℕ)
    (scale : (g : SignedBankSlot β) → Fin (steps g) → ℕ)
    (height : ℕ)
    (poolOf : (Σ g : SignedBankSlot β, Fin (steps g)) → Pool)
    (available : Pool → Finset ℕ)
    (ambient forbidden : Finset ℕ)
    (hstart : ∀ g, core g 0 = g.1.1)
    (hfinish : ∀ g, core g (steps g) = 1)
    (hcore : ∀ g i, i ≤ steps g → 0 < core g i)
    (hscale : ∀ g i, 0 < scale g i)
    (hsource : ∀ g i, scale g i * core g i.1 ≤ height)
    (htarget : ∀ g i, scale g i * core g (i.1 + 1) ≤ height)
    (hcapacity : ∀ p,
      Fintype.card {r : (Σ g : SignedBankSlot β, Fin (steps g)) // poolOf r = p} ≤
        (available p).card)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (available p) (available q))
    (hprime : ∀ p q, q ∈ available p → q.Prime)
    (hlarge : ∀ p q, q ∈ available p → height < q)
    (hlegal : ∀ g (i : Fin (steps g)) q,
      q ∈ available (poolOf ⟨g, i⟩) → ∀ b : Bool,
        q * (scale g i * core g (if b then i.1 + 1 else i.1)) ∈ ambient)
    (hguard : ∀ g (i : Fin (steps g)) q,
      q ∈ available (poolOf ⟨g, i⟩) → ∀ b : Bool,
        q * (scale g i * core g (if b then i.1 + 1 else i.1)) ∉ forbidden) :
    ∃ R : MarkedBankPaths P β,
      R.steps = steps ∧ R.core = core ∧ HEq R.scale scale ∧ R.height = height ∧
      ∀ g b, R.signedState g b ⊆ ambient ∧ Disjoint forbidden (R.signedState g b) := by sorry
