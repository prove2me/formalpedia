-- Prove2me | Definitions.Def_erdos390_marked_bank_paths
-- name    : erdos390_marked_bank_paths
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-16T15:09:51.038812+00:00
-- url     : https://prove2.me/theorems/a2c9df9f-640d-4949-86d7-5269f8d1446a
-- title:
--   Prime-marked integer paths for a signed correction bank
-- statement:
--   Let $P$ be a finite set of natural numbers, with a budget $\beta_p$ at each coordinate. There are $\beta_p$ slots of each sign at $p$. For every slot $g$ choose a finite core path
--   $$c_{g,0}=p,\qquad c_{g,m_g}=1,\qquad c_{g,i}>0,$$
--   positive integer scales $s_{g,i}$, and prime markers $\ell_{g,i}$. All markers are distinct, and there is a common bound $H$ such that
--   $$s_{g,i}c_{g,i}\le H,\quad s_{g,i}c_{g,i+1}\le H<\ell_{g,i}.$$
--   The two endpoint factors of edge $i$ are $\ell_{g,i}s_{g,i}c_{g,i}$ and $\ell_{g,i}s_{g,i}c_{g,i+1}$. A downward state contains one endpoint from each edge. Negative slots keep this orientation, while positive slots reverse it; state zero is always the state charged in the initial bank.
--
--   This is a finite arithmetic interface for the source's paths. The common scale accommodates its terminal move with actual cofactors $4$ and $2$ while the core path goes from $2$ to $1$. Neither a valuation-change identity nor disjointness of factor states is a field. Interval placement, guards, and asymptotic existence are separate obligations.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, pinned commit 61325b10bbdc29f4fb5e0618b414b9f2189333ad, Section 5, complete-rough-signature, bank-ordinary-cell, bank-four-bottom-pools, bank-unit-ratio, bank-unit-vector, Lemma bank-donor-injection, and the distinct-marker argument immediately before subsection bank-precharge. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . See also BankPathAlgebra.lean, BankPaperComponents.lean, and BankPaperExactificationState.lean in 390/lean/Erdos390/WholePaper/.

import Definitions.Def_erdos390_signed_bank

open scoped BigOperators

namespace Erdos390.WholePaper
noncomputable section

/-- Arithmetic data for prime-to-one paths with globally distinct prime markers.
The scale allows the last core move `2 → 1` to use actual cofactors `4 → 2`. -/
structure MarkedBankPaths (P : Finset ℕ) (β : ↑P → ℕ) where
  steps : SignedBankSlot β → ℕ
  core : SignedBankSlot β → ℕ → ℕ
  scale : (g : SignedBankSlot β) → Fin (steps g) → ℕ
  marker : (Σ g : SignedBankSlot β, Fin (steps g)) → ℕ
  height : ℕ
  core_start : ∀ g, core g 0 = g.1.1
  core_finish : ∀ g, core g (steps g) = 1
  core_pos : ∀ g i, i ≤ steps g → 0 < core g i
  scale_pos : ∀ g i, 0 < scale g i
  marker_prime : ∀ r, (marker r).Prime
  marker_injective : Function.Injective marker
  marker_large : ∀ r, height < marker r
  source_small : ∀ g i, scale g i * core g i.1 ≤ height
  target_small : ∀ g i, scale g i * core g (i.1 + 1) ≤ height

namespace MarkedBankPaths

def endpoint {P : Finset ℕ} {β : ↑P → ℕ} (R : MarkedBankPaths P β)
    (g : SignedBankSlot β) (b : Bool) (i : Fin (R.steps g)) : ℕ :=
  R.marker ⟨g, i⟩ * (R.scale g i * R.core g (if b then i.1 + 1 else i.1))

def downwardState {P : Finset ℕ} {β : ↑P → ℕ} (R : MarkedBankPaths P β)
    (g : SignedBankSlot β) (b : Bool) : Finset ℕ := by
  classical
  exact Finset.univ.image (R.endpoint g b)

/-- Positive slots reverse the downward path; negative slots keep its orientation.
In both cases `false` denotes the charged initial state. -/
def signedState {P : Finset ℕ} {β : ↑P → ℕ} (R : MarkedBankPaths P β)
    (g : SignedBankSlot β) (b : Bool) : Finset ℕ :=
  match g.2 with
  | .inl _ => R.downwardState g (!b)
  | .inr _ => R.downwardState g b

end MarkedBankPaths
end
end Erdos390.WholePaper


