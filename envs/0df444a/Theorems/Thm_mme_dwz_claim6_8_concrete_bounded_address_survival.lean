-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_concrete_bounded_address_survival
-- name    : mme_dwz_claim6_8_concrete_bounded_address_survival
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:20:18.797308+00:00
-- url     : https://prove2.me/theorems/25d2f133-dc21-4847-b7ff-9efc1c6dbd28
-- title:
--   DWZ Claim 6.8: bounded-address hashing leaves seven eighths non-holes
-- statement:
--   Let $p$ be an odd prime larger than the maximum address level, and condition the Duan--Wu--Zhou asymmetric hash on one distinguished bounded natural address $I$ and a fixed low-side address $K$. Let $C$ be a finite set of competing addresses, every one distinct from $I$, and call a hash parameter bad only if a member of $C$ collides with the conditioned low-side hash. If $8|C|\le p$, then
--
--   $$
--   8 |\{w:w\text{ is bad}\}|\le |\operatorname{ZMod}(p)^{n+1}|.
--   $$
--
--   Thus at most one eighth of the conditioned hash-parameter space is bad. This concrete finite interface isolates the remaining paper-specific task: enumerate the compatible competing addresses and establish the modulus budget $8|C|\le p$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/abs/2210.10173, Lemma 3.11 and Claim 6.8 (printed pp. 56-57 / PDF pp. 57-58).

import Mathlib
import Theorems.Thm_mme_dwz_lemma3_11_bounded_address_collision_fiber
import Theorems.Thm_mme_dwz_claim6_8_one_eighth_from_collision_budget
open BigOperators
set_option autoImplicit false

theorem mme_dwz_claim6_8_concrete_bounded_address_survival
    {p n levelSum : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (I K : Fin (n + 1) → Fin (levelSum + 1))
    (candidates : Finset (Fin (n + 1) → Fin (levelSum + 1)))
    (hdistinct : ∀ A ∈ candidates, A ≠ I)
    (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad] :
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w A => b0 + ∑ t, ((A t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w0 w C =>
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t,
            ((levelSum : ZMod p) - (C t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w =>
        2 * (∑ t, ((I t).val : ZMod p) * w t) -
          ∑ t, ((levelSum : ZMod p) - (K t).val) * w t
    (∀ w, bad w →
      ∃ A ∈ candidates, hX w A = hZ (conditionedW0 w) w K) →
    8 * candidates.card ≤ p →
    8 * (Finset.univ.filter bad).card ≤
      Fintype.card (Fin (n + 1) → ZMod p) := by sorry
