-- Prove2me | Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
-- name    : WittVector.ringHom_map_frobenius_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c1dcd8e1-638d-57b0-afc1-1794381d2905
-- title:
--   Ring maps W(F)→ W(k) commute with Frobenius
-- statement:
--   Let $p$ be a prime, let $F$ be a finite field of characteristic $p$, and let $k$ be a commutative ring of characteristic $p$ that is perfect, i.e. its $p$-power map is bijective (`PerfectRing k p`). Let $\iota : W(F) \to W(k)$ be any ring homomorphism between the rings of $p$-typical Witt vectors, where no continuity, linearity or compatibility hypothesis is imposed, and let $x \in W(F)$. Then $\iota$ commutes with the Witt vector Frobenius endomorphism: $\iota(\mathrm{F}\,x) = \mathrm{F}(\iota\,x)$, with `WittVector.frobenius` taken on $W(F)$ on the left and on $W(k)$ on the right. The two source and target types are allowed to live in different universes.
--
--   For $F = \mathbb{F}_{p^d}$ this says that the at most $d$ embeddings of the ring of integers of the unramified extension of $\mathbb{Q}_p$ of degree $d$ into $W(k)$ are automatically Frobenius-equivariant. It is used in the Čerednik–Drinfeld part of the development, in the analysis of Cartier quadruples over special formal schemes, where Witt-vector structure maps have to be compared with the Frobenius of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_ringHom_map_frobenius_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem WittVector.ringHom_map_frobenius_of_finite
    (p : ℕ) [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
    ι (WittVector.frobenius x) = WittVector.frobenius (ι x) := by sorry
