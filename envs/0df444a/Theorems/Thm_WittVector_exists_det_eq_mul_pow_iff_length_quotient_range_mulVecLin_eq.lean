-- Prove2me | Theorems.Thm_WittVector_exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq
-- name    : WittVector.exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/13e20148-bc66-52dd-909b-5a3e546744fb
-- title:
--   p-adic valuation of detγ as Witt-vector colength
-- statement:
--   Let $p$ be a prime, and let $K$ be a field of characteristic $p$ which is perfect in the sense that the $p$-th power map (Frobenius) is bijective. Let $c \colon \mathbb{Z}_p \to \mathbb{W}(K)$ be a ring homomorphism into the ring of Witt vectors of $K$, let $\gamma$ be a $2 \times 2$ matrix with entries in $\mathbb{Z}_p$, indexed by `Fin 2`, and let $h$ be a natural number. The assertion is an equivalence of two conditions. The first is that there exists a unit $u \in \mathbb{Z}_p^{\times}$ with $\det \gamma = u\,p^{h}$, i.e.\ that $\det\gamma$ is nonzero of $p$-adic valuation exactly $h$. The second is that the $\mathbb{W}(K)$-module length of the quotient of the free module $\mathbb{W}(K)^2$ (written as functions `Fin 2 → WittVector p K`) by the range of the $\mathbb{W}(K)$-linear map $v \mapsto \gamma^{c} v$, where $\gamma^{c}$ is the matrix obtained from $\gamma$ by applying $c$ entrywise, equals $h$. Since the length takes values in $\mathbb{N} \cup \{\infty\}$, the case $\det\gamma = 0$ is covered: the quotient then has infinite length and neither side holds.
--
--   This is the statement that the colength over $\mathbb{W}(K)$ of an integral $p$-adic $2 \times 2$ matrix acting on $\mathbb{W}(K)^2$ computes the $p$-adic valuation of its determinant, $\mathbb{W}(K)$ being a discrete valuation ring with uniformiser $p$ when $K$ is perfect of characteristic $p$. It serves as the index (height) computation in the Čerednik–Drinfeld material, where it is used to read off the valuation of the determinant of a matrix from the height of an isogeny or from a rigidification datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt Padic

theorem WittVector.exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (c : ℤ_[p] →+* WittVector p K) (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h : ℕ) :
    (∃ u : ℤ_[p]ˣ, γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h) ↔
      Module.length (WittVector p K)
        ((Fin 2 → WittVector p K) ⧸ LinearMap.range (Matrix.mulVecLin (γ.map c))) = h := by sorry
