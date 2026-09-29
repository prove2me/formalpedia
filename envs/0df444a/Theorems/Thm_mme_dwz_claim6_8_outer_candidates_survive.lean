-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_outer_candidates_survive
-- name    : mme_dwz_claim6_8_outer_candidates_survive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:11:54.193732+00:00
-- url     : https://prove2.me/theorems/e270b2b6-0bb1-49fa-845a-10b5bfa4f2ef
-- title:
--   DWZ Claim 6.8: injective outer candidates preserve the one-eighth hash bound
-- statement:
--   Fix an odd prime modulus $p$, a bounded coarse $Z$-address $K$, and a finite type of source outer objects. Suppose the bounded $X$-address map from outer objects is injective. For a retained object $A_0$, let $\mathcal C$ be the outer objects which differ from $A_0$ and are compatible with a fixed small block. Condition the DWZ affine hash on the retained equality $h_X(I_{A_0})=h_Z(K)$. If every bad parameter is witnessed by a collision with the address of some $A\in\mathcal C$, and $8|\mathcal C|\le p$, then
--
--   $$
--   8|\{w:w\text{ is bad}\}|\le |\operatorname{ZMod}(p)^{n+1}|.
--   $$
--
--   Thus at most one eighth of the conditioned hash parameters are bad. The theorem projects literal source outer objects to the already-formalized bounded-address interface without cardinality loss and proves that the retained address is absent. For Claim 6.8, `bad` may be instantiated with the hole event only after separately proving the displayed collision-coverage premise; no hole or tensor-survival conclusion is hidden in the statement.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Claim 6.8 (printed pp. 56-57, PDF pp. 57-58), using Lemma 3.11; https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_claim6_8_concrete_bounded_address_survival

open BigOperators

set_option autoImplicit false

theorem mme_dwz_claim6_8_outer_candidates_survive
    {p n levelSum : ℕ} [Fact p.Prime]
    {Outer : Type*} [Fintype Outer] [DecidableEq Outer]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (addressX : Outer → Fin (n + 1) → Fin (levelSum + 1))
    (haddressX : Function.Injective addressX)
    (retained : Outer)
    (K : Fin (n + 1) → Fin (levelSum + 1))
    (compatible : Outer → Prop) [DecidablePred compatible]
    (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad] :
    let outerCandidates :=
      Finset.univ.filter (fun A : Outer ↦ A ≠ retained ∧ compatible A)
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w0 w C ↦
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, ((levelSum : ZMod p) - (C t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w ↦
        2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
          ∑ t, ((levelSum : ZMod p) - (K t).val) * w t
    (∀ w, bad w →
      ∃ A ∈ outerCandidates,
        hX w (addressX A) = hZ (conditionedW0 w) w K) →
    8 * outerCandidates.card ≤ p →
    8 * (Finset.univ.filter bad).card ≤
      Fintype.card (Fin (n + 1) → ZMod p) := by sorry
