-- Prove2me | Theorems.Thm_mme_recursive_yz_boundary_scaled_piece_eventual_witness
-- name    : mme_recursive_yz_boundary_scaled_piece_eventual_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T10:41:08.515341+00:00
-- url     : https://prove2.me/theorems/04f8c46e-ec05-4a44-8908-739cf0df467d
-- title:
--   Scaled boundary cell pieces have eventual finite witnesses below their entropy rate
-- statement:
--   Let $B$ be an exact boundary profile of length $L>0$ at complete-split level $2$. It has multiplicities $B_s$ over the two-letter fine words $s$, and $\mathrm{ones}(s)$ is the number of grade-one letters of $s$. Let $B^{(t)}$ be any boundary profiles of length $Lt$ with multiplicities $t B_s$, i.e. $B$ scaled by $t$. Fix a free mode $z$ and $\tau \ge 0$. Define the per-position rate
--   $$R(B,\tau) = \exp\Big(\tau \sum_s -\tfrac{B_s}{L}\log\tfrac{B_s}{L}\Big)\cdot 5^{\tau \sum_s B_s\,\mathrm{ones}(s)/L}.$$
--
--   **Statement.** For every $0 < v < R(B,\tau)$, eventually in $t$ the boundary cell piece $B^{(t)}.\mathrm{tensor}(z)$ has a finite six-symmetrized witness at length $Lt$ with base $v$. That is, there is a direct sum of matrix multiplication tensors restricting to its six-symmetrization with $\sum (abc)^\tau \ge v^{6Lt}$.
--
--   The piece contains a single matrix multiplication tensor $\langle 1,1,D_t\rangle$ (in some orientation), where $D_t$ is the multinomial coefficient times $5^{t\sum_s B_s \mathrm{ones}(s)}$. The multinomial is at least $e^{tLH}$ up to a polynomial factor, so $D_t^{\tau} \ge v^{Lt}$ for all large $t$.
--
--   This supplies the boundary child values of the More-Asymmetry regional extraction for the Duan–Wu–Zhou fourth-power components.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.Boundary
  MME.CompleteSplit MME.DWZRestrictedValue

universe u

set_option autoImplicit false

theorem mme_recursive_yz_boundary_scaled_piece_eventual_witness {K : Type u} [Field K] {L : ℕ}
    (B : Profile 2 L) (hL : 0 < L) (Bt : ∀ t : ℕ, Profile 2 (L * t))
    (hBt : ∀ t s, (Bt t).count s = B.count s * t) (z : Fin 3) (tau v : ℝ)
    (htau : 0 ≤ tau) (hv : 0 < v)
    (hvV : v < Real.exp (tau * ∑ s, Real.negMulLog ((B.count s : ℝ) / L)) *
      (5 : ℝ) ^ (tau * ((∑ s, B.count s * ones s : ℕ) : ℝ) / L)) :
    ∀ᶠ t : ℕ in atTop,
      SixFiniteWitness TensorObj.Restrict ((Bt t).tensor K z) (L * t) tau v := by sorry
