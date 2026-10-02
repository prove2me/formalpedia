-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter38_chapter38
-- name    : ProofsInTheBook.Chapter38.chapter38
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:28.608218+00:00
-- url     : https://prove2.me/theorems/e289f44b-022c-4560-864d-3f7a19728796
-- title:
--   Singleton, Hamming, and Gilbert–Varshamov coding bounds
-- statement:
--   Let $q,n,t,d\in\mathbb N$ satisfy $q>0$, $d>0$, and $2t<d$. Let $C$ be a finite set of words in $\operatorname{Fin}(q)^n$, with Hamming distance at least $d$ between distinct words. Let $V_q(n,s)$ be the cardinality of the radius-$s$ Hamming ball centered at the zero word, for any $s\in\mathbb N$. Then
--   $$|C|\le q^{\max(n+1-d,0)},\qquad |C|V_q(n,t)\le q^n,$$
--   and there exists a finite code $C'\subseteq\operatorname{Fin}(q)^n$ whose distinct words also have distance at least $d$ and which satisfies
--   $$q^n\le |C'|V_q(n,d-1).$$
--
--   These are finite Singleton, sphere-packing, and Gilbert–Varshamov bounds. No asymptotic capacity or entropy formula is asserted.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 42, “Communicating without errors”, pp. 291–300 (https://doi.org/10.1007/978-3-662-57265-8_42). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter38.lean#L367. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter38
open Finset
open ProofsInTheBook.Chapter38

theorem ProofsInTheBook.Chapter38.chapter38 {q n t d : ℕ} (hq : 0 < q) {code : Finset (QaryWord q n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd_pos : 0 < d) (ht : 2 * t < d) :
    code.card ≤ q ^ (n + 1 - d) ∧
      code.card * qaryHammingBallVolume q n t ≤ q ^ n ∧
        ∃ gvCode : Finset (QaryWord q n),
          (∀ c₁ ∈ gvCode, ∀ c₂ ∈ gvCode, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) ∧
            q ^ n ≤ gvCode.card * qaryHammingBallVolume q n (d - 1) := by sorry
