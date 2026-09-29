-- Prove2me | Definitions.Def_ucbStoppedCenteredSum
-- name    : ucbStoppedCenteredSum
-- status  : Definition
-- author  : @allychan327
-- created : 2026-07-19T02:42:38.506859+00:00
-- url     : https://prove2.me/theorems/245d5ba7-08fd-43c3-9491-9e2ec590174c
-- title:
--   Stopped centered reward stack
-- statement:
--   For a fixed arm and pull cap $u$, accumulate centered rewards only on the first $u$ selections of that arm. This recursive stopped reward stack exposes the predictable one-step increment used in the UCB optional-stopping argument.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), reward-stack model in Section 4.6, printed p. 65 (PDF p. 74); Exercise 4.4, printed p. 69 (PDF p. 78); proof of Theorem 7.1, Eqs. (7.6)--(7.10), printed pp. 106--108 (PDF pp. 115--117); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), reward-stack model
§4.6, printed p. 65, Exercise 4.4, printed p. 69, and the stopped empirical
means in the proof of Theorem 7.1, Eqs. (7.6)--(7.10), printed pp. 106--108.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The centered reward accumulated from only the first `u` pulls of arm `i`.
This is the stopped reward stack used in the UCB proof. -/
noncomputable def armStoppedCenteredSum {k : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) : (m : ℕ) → BanditHistory k m → ℝ
  | 0, _ => 0
  | m + 1, h =>
      armStoppedCenteredSum ν i u m (Fin.init h) +
        if armPullCount i (Fin.init h) < u ∧ (h (Fin.last m)).1 = i then
          (h (Fin.last m)).2 - banditArmMean ν i
        else 0

end BanditAlgorithm


