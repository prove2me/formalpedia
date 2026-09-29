-- Prove2me | Theorems.Thm_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add
-- name    : WittVector.exists_eq_sum_iterate_verschiebung_teichmuller_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/ab8c9849-1984-5a46-9981-63a1fc521610
-- title:
--   Truncated Teichmüller expansion of a Witt vector
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring, let $w$ be a Witt vector in $W(B) =$ `WittVector p B`, and let $N$ be a natural number. The assertion is that there exists a Witt vector $w' \in W(B)$ with
--   $$w \;=\; \sum_{n < N} V^{n}\bigl([\,w_n\,]\bigr) \;+\; V^{N} w',$$
--   where the sum is over $n$ in `Finset.range N`, $w_n$ denotes the $n$-th Witt coefficient `w.coeff n`, $[\,a\,]$ denotes the Teichmüller element `WittVector.teichmuller p a` of $W(B)$, and $V^{n}$ means the $n$-fold iterate of the underlying function of the Verschiebung additive map `WittVector.verschiebung : WittVector p B →+ WittVector p B`. Both the addition and the finite sum are those of the Witt vector ring $W(B)$. No hypothesis beyond commutativity of $B$ is imposed: in particular $B$ need not be of characteristic $p$, nor torsion-free, nor $p$-adically complete, and the statement is purely existential, giving no formula for $w'$ (the witness produced is the $N$-fold shift of $w$).
--
--   This is the truncated Teichmüller (digit) expansion of a Witt vector, the basic device for writing an element of $W(B)$ as a finite sum of Verschiebungs of Teichmüller representatives modulo the image of $V^{N}$. It is used in the work on formal $\mathcal{O}_D$-modules in the Cerednik–Drinfeld part of the development, where endomorphisms are analysed through their effect on such expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WittVector.exists_eq_sum_iterate_verschiebung_teichmuller_add
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (w : WittVector p B) (N : ℕ) :
    ∃ w' : WittVector p B,
      w = (∑ n ∈ Finset.range N, (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[n]
            (WittVector.teichmuller p (w.coeff n))) +
          (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[N] w' := by sorry
