-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_random_model_strong_convergence
-- name    : ZigZagStrong.ZigZag.random_model_strong_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:08.598463+00:00
-- url     : https://prove2.me/theorems/36825f82-6d71-42fa-bd9c-c943ec56dc15
-- title:
--   Theorem 2.4 — strong convergence in all three random models
-- statement:
--   Let $r$ be the number of independent generators. Sample independent uniform permutations, perfect matchings, or involutions, and restrict their permutation operators to the orthogonal complement of constants. Their limiting tuples are the regular generators of $F_r$ in the permutation case and of $\mathbb Z_2^{*r}$ in the other two cases.
--   $$u_n|_{1^\perp}\ \longrightarrow\ \lambda\qquad\text{strongly in probability}.$$
--   The statement retains all three laws. Matching sizes run through all sufficiently large even integers. This is the common random-model input to zig-zag spectral convergence.
--
--   Differences from the source:
--   - encoding: The limit n tends to infinity, along even n for matchings → Sizes n+2 for permutations/involutions and 2*(n+1) for matchings; reason: Removing finitely many undefined zero-dimensional spectral cases changes no asymptotic statement and includes every sufficiently large admissible size.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 2.4, p. 9.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem random_model_strong_convergence (r : ℕ) :
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
    (fun _ σ => StrongConv.sModel σ) (StrongConv.sLimit r) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Matching (2*(n+1))))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) := by sorry

end ZigZagStrong.ZigZag
