-- Prove2me | Definitions.Def_mme_stothers_phi224_profile_data
-- name    : mme_stothers_phi224_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T09:12:03.947697+00:00
-- url     : https://prove2.me/theorems/f93db1f2-c842-43a4-bdd1-8d421df41d69
-- title:
--   Exact type-2 profile data for the phi_224 constituent
-- statement:
--   This module records the nine ordered first-square grades in the $\varphi_{224}$ decomposition, in source order
--
--   $$
--   004,013,022,103,112,121,202,211,220.
--   $$
--
--   For integers $\alpha,\beta,\gamma,\delta\ge0$ with $\alpha+2\beta+\gamma+\delta=N$, the exact length-$2N$ profile has multiplicities
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha).
--   $$
--
--   The module defines exact and same-marginal profile words, their three projected five-grade histograms, and the cyclic three-orientation edge and vertex types used by the type-2 Salem–Spencer extraction. The factor $2\delta$ at the central $112$ type is essential: it makes the total profile length exactly $2N$ and yields the paper's middle marginal $2\beta+2\delta$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 setup on pp. 359–360 and Lemma 5.1(iv), displayed phi_224 marginals on pp. 365–366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

open BigOperators

namespace MME.StothersFourth.Phi224

set_option autoImplicit false

/-- The nine first-square grades in the source order
`004,013,022,103,112,121,202,211,220`.  The complementary second-square
grade is obtained by subtracting from `(2,2,4)`. -/
def pattern : Fin 9 → Fin 3 → Fin 5
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 4
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 3
  | 2, 0 => 0
  | 2, 1 => 2
  | 2, 2 => 2
  | 3, 0 => 1
  | 3, 1 => 0
  | 3, 2 => 3
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 2
  | 5, 0 => 1
  | 5, 1 => 2
  | 5, 2 => 1
  | 6, 0 => 2
  | 6, 1 => 0
  | 6, 2 => 2
  | 7, 0 => 2
  | 7, 1 => 1
  | 7, 2 => 1
  | 8, 0 => 2
  | 8, 1 => 2
  | 8, 2 => 0

/-- The symmetric integral profile from Lemma 5.1(iv).  The central
`112` type occurs `2 * delta` times, so the total length is `2 * N` when
`alpha + 2 * beta + gamma + delta = N`. -/
def profileMultiplicity
    (alpha beta gamma delta : ℕ) : Fin 9 → ℕ
  | 0 => alpha
  | 1 => beta
  | 2 => gamma
  | 3 => beta
  | 4 => 2 * delta
  | 5 => beta
  | 6 => gamma
  | 7 => beta
  | 8 => alpha

/-- The three projected histograms printed in the `phi_224` proof. -/
def marginalMultiplicity
    (alpha beta gamma delta : ℕ) : Fin 3 → Fin 5 → ℕ
  | 0, 0 => alpha + beta + gamma
  | 0, 1 => 2 * beta + 2 * delta
  | 0, 2 => alpha + beta + gamma
  | 0, 3 => 0
  | 0, 4 => 0
  | 1, 0 => alpha + beta + gamma
  | 1, 1 => 2 * beta + 2 * delta
  | 1, 2 => alpha + beta + gamma
  | 1, 3 => 0
  | 1, 4 => 0
  | 2, 0 => alpha
  | 2, 1 => 2 * beta
  | 2, 2 => 2 * gamma + 2 * delta
  | 2, 3 => 2 * beta
  | 2, 4 => alpha

/-- A length-`2N` word of the nine fine types. -/
abbrev ProfileWord (N : ℕ) := Fin (2 * N) → Fin 9

/-- The grade word visible in one tensor mode. -/
def modeWord {N : ℕ} (w : ProfileWord N) (i : Fin 3) :
    Fin (2 * N) → Fin 5 :=
  fun j ↦ pattern (w j) i

/-- Words with the exact symmetric source profile. -/
def ExactProfileWord
    (N alpha beta gamma delta : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ r : Fin 9,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          profileMultiplicity alpha beta gamma delta r}

/-- The larger family of words with the same three projected histograms. -/
def MarginalProfileWord
    (N alpha beta gamma delta : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ modeWord w i j = s)).card =
          marginalMultiplicity alpha beta gamma delta i s}

/-- One exact address in each of the three cyclic orientations. -/
def CyclicExactEdge
    (N alpha beta gamma delta : ℕ) : Type :=
  ExactProfileWord N alpha beta gamma delta ×
    (ExactProfileWord N alpha beta gamma delta ×
      ExactProfileWord N alpha beta gamma delta)

/-- One vertex of the cyclic construction contains one mode word from each
orientation. -/
def CyclicModeWord (N : ℕ) : Type :=
  (Fin (2 * N) → Fin 5) ×
    ((Fin (2 * N) → Fin 5) × (Fin (2 * N) → Fin 5))

/-- The three cyclic mode projections of an exact edge. -/
def cyclicModeWord
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ => (modeWord e.1.1 0, (modeWord e.2.1.1 2, modeWord e.2.2.1 1))
  | ⟨1, _⟩ => (modeWord e.1.1 1, (modeWord e.2.1.1 0, modeWord e.2.2.1 2))
  | ⟨2, _⟩ => (modeWord e.1.1 2, (modeWord e.2.1.1 1, modeWord e.2.2.1 0))
  | ⟨_ + 3, h⟩ => absurd h (by omega)

end MME.StothersFourth.Phi224


