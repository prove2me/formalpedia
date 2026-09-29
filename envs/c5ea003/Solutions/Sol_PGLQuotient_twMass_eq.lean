-- Prove2me | solution 1 for PGLQuotient.twMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:38:56.785214+00:00
-- url     : https://prove2.me/submissions/587d1529-730c-4236-837c-b7bd45833e11

-- Sol generated from Algebra/PGLQuotient/VertexVolumeGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
import Theorems.Thm_PGLQuotient_NumDen_step
import Theorems.Thm_PGLQuotient_twMass_succ

/-!
# The vertex volume of the standard arithmetic quotient of `PGL_d`, in arbitrary rank

This file proves the headline computation in **arbitrary rank `d`**: with the Haar measure
normalised so that a maximal compact subgroup has volume `1`, the vertex volume of the standard
nonuniform arithmetic quotient of the affine Bruhat–Tits building of `PGL_d(F_q((t^{-1})))` is

`∑_λ 1/|Aut λ| = d / (P(d) · P(d-1))`,   `P(n) = ∏_{k=1}^{n} (q^k - 1)`

(`vertexVolume_general`, and `vertexVolume_general_rank` for the `d`-indexed form), together
with its `PGL`-normalised variant `(q-1) · ∑_λ 1/|Aut λ|` (`vertexVolume_general_pgl`).

The proof is the promised cut-set recursion, run on the two-parameter twisted mass of
`Algebra.PGLQuotient.TwistedWeight`:

* `twMass_succ`: peeling the top row of a dominant coweight turns the rank-`(n+2)` twisted mass
  into a combination of two rank-`(n+1)` twisted masses (the zero-gap branch and the
  positive-gap branch, the latter summed as a geometric series in the gap);
* `twMass_eq`: solving that recursion by induction on the rank, the closed form being
  `NumV/DenV` from `Algebra.PGLQuotient.VolumeAlgebra`;
* specialising `c = j = 0` gives the vertex volume, since `NumV q n 0 0 = (n+1)·P(n)` and
  `DenV q n 0 0 = P(n+1)·P(n)·P(n)`.

For `d = 2, 3` this recovers `heightZeta_rank_two` (at `s = 0`) and `vertexVolume_rank_three`.
-/

open PGLQuotient

open Finset

variable {q : ℝ}
















open PGLQuotient in
theorem solution(hq : 1 < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 1), twWeight q c j g = NumV q n c j / DenV q n c j := by
  induction n generalizing c j with
  | zero =>
      have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
      have hval : ∀ g : Vertex 1, twWeight q c j g = (q ^ (1 + j) - 1)⁻¹ := by
        intro g
        have hlam : ∀ i : ℕ, lam g i = 0 := by
          intro i
          unfold lam
          simp
        have hend : endDim g = 1 := by
          unfold endDim
          simp [hlam]
        have hsig : sigmaExp g = 0 := by
          unfold sigmaExp
          simp [hlam]
        have hfb : firstBlockSize g = 1 := by
          unfold firstBlockSize
          simp [hlam]
        have hbr : blockRank g 0 = 1 := by
          unfold blockRank
          simp [hlam, Finset.filter_singleton]
        have hbp : blockProdShift q j g = 1 - q⁻¹ ^ (1 + j) := by
          unfold blockProdShift
          rw [Finset.prod_range_one, hbr, if_pos rfl]
        unfold twWeight
        rw [hend, hsig, hfb, hbp]
        congr 1
        rw [Nat.mul_zero, Nat.add_zero, Nat.mul_one, inv_pow]
        have : q ^ (1 + j) ≠ 0 := by positivity
        field_simp
      have hsub : ∀ b : Vertex 1, b = (fun i => i.elim0) := fun b => funext (fun i => i.elim0)
      rw [tsum_eq_single (fun i => i.elim0) (fun b hb => absurd (hsub b) hb), hval]
      unfold NumV DenV
      simp [Gpoly, Jfac, Pfac, Cfac]
  | succ m ih =>
      rw [twMass_succ hq m c j, ih (c + 1) (j + 1), ih (c + 1) 0, NumDen_step hq]
