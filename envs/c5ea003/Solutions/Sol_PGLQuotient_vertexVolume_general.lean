-- Prove2me | solution 1 for PGLQuotient.vertexVolume_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:48.832899+00:00
-- url     : https://prove2.me/submissions/fbecb64a-9108-4ab1-b9e1-c359414a55bb

-- Sol generated from Algebra/PGLQuotient/VertexVolumeGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
import Theorems.Thm_PGLQuotient_Jfac_zero_right
import Theorems.Thm_PGLQuotient_NumV_zero_right
import Theorems.Thm_PGLQuotient_Pfac_pos
import Theorems.Thm_PGLQuotient_twMass_eq
import Theorems.Thm_PGLQuotient_twWeight_zero_zero

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
theorem solution(hq : 1 < q) (n : ℕ) :
    ∑' g : Vertex (n + 1), vertexWeight q g = (n + 1) / (Pfac q (n + 1) * Pfac q n) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h1 : ∑' g : Vertex (n + 1), vertexWeight q g = NumV q n 0 0 / DenV q n 0 0 := by
    rw [← twMass_eq hq n 0 0]
    exact tsum_congr (fun g => (twWeight_zero_zero g).symm)
  have hNum : NumV q n 0 0 = (n + 1) * Pfac q n := by
    rw [NumV_zero_right]
    simp [Finset.sum_const, Finset.card_range]
    ring
  have hDen : DenV q n 0 0 = Pfac q (n + 1) * Pfac q n * Pfac q n := by
    unfold DenV
    rw [Jfac_zero_right]
    congr 1
    unfold Cfac Pfac
    exact Finset.prod_congr rfl (fun k _ => by rw [Nat.zero_add])
  have hP : (0:ℝ) < Pfac q n := Pfac_pos hq n
  have hP1 : (0:ℝ) < Pfac q (n + 1) := Pfac_pos hq (n + 1)
  rw [h1, hNum, hDen]
  field_simp
