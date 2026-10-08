-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter30_total_sum_eq_good_sum_of_bad_sign_reversing
-- name    : ProofsInTheBook.Chapter30.total_sum_eq_good_sum_of_bad_sign_reversing
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:27:34.33468+00:00
-- url     : https://prove2.me/theorems/edf5796a-76b2-4131-a674-8cb84ed8662f
-- title:
--   Cancellation of a finite bad subfamily in a torsion-free additive group
-- statement:
--   Let A be a finite type with decidable equality, and let R be an additive commutative group whose addition is torsion-free. Let $\mathrm{bad}:A\to\mathrm{Prop}$ be decidable. Suppose a bijection $\tau_B:B\simeq B$ is supplied on $B=\{x\in A:\mathrm{bad}(x)\}$, together with $w:A\to R$ satisfying $w(\tau_B(x))=-w(x)$ for every $x\in B$. Then $$\sum_{x\in A}w(x)=\sum_{\substack{x\in A\\\neg\mathrm{bad}(x)}}w(x).$$ The bad-subfamily bijection and sign-reversal identity are hypotheses; the bijection need not be an involution.
-- source:
--   Exact repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L96. PathCountSystem hypotheses: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L435. Explicit scope limitation: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L578. Repository topic: “Lattice paths and determinants.” No edition-specific chapter mapping or geometric application is asserted.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter30
open ProofsInTheBook.Chapter30
open Matrix BigOperators

theorem ProofsInTheBook.Chapter30.total_sum_eq_good_sum_of_bad_sign_reversing {α R : Type*} [Fintype α]
    [DecidableEq α] [AddCommGroup R] [IsAddTorsionFree R]
    (bad : α → Prop) [DecidablePred bad] (τbad : {x : α // bad x} ≃ {x : α // bad x})
    (w : α → R) (hw : ∀ x : {x : α // bad x}, w (τbad x).1 = -w x.1) :
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := by sorry
