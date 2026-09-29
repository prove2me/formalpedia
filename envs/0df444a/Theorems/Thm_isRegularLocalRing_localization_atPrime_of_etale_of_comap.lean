-- Prove2me | Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
-- name    : isRegularLocalRing_localization_atPrime_of_etale_of_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/eaa9c4ea-af9a-5289-9430-f8572db73381
-- title:
--   Étale descent of regularity to localizations at primes
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra which is étale (in Mathlib's sense: formally étale and of finite presentation over $A$), and let $q$ be a prime ideal of $B$. Write $p = q \cap A$ for the contraction of $q$ along the structure map $A \to B$, i.e. `q.comap (algebraMap A B)`. The hypothesis is that the localization of $A$ at $p$, `Localization.AtPrime (q.comap (algebraMap A B))`, is a regular local ring. The conclusion is that the localization `Localization.AtPrime q` of $B$ at $q$ is a regular local ring as well. No Noetherian hypothesis is imposed on $A$ or $B$ beyond what regularity of $A_p$ provides: regularity of a local ring in the sense used here already entails that the ring is Noetherian, and Noetherianity of $B_q$ is derived in the course of the proof from the fact that $B_q$ is essentially of finite type over $A_p$.
--
--   This is the statement that étale morphisms preserve regularity of local rings, in the fibre-wise form: the local ring of the target at a prime is regular as soon as the local ring of the source at the image prime is. It is used to pass regularity along étale presentations, being cited in the treatment of regularity of stalks of smooth schemes over a discrete valuation ring and in the corresponding statement for standard smooth algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by sorry
