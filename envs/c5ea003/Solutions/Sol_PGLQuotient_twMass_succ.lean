-- Prove2me | solution 1 for PGLQuotient.twMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:36:45.988222+00:00
-- url     : https://prove2.me/submissions/64e96132-168d-4314-a6b1-213f52bac9d5

-- Sol generated from Algebra/PGLQuotient/VertexVolumeGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
import Theorems.Thm_PGLQuotient_gapRatio_lt_one
import Theorems.Thm_PGLQuotient_gapRatio_nonneg
import Theorems.Thm_PGLQuotient_prod_gapRatio
import Theorems.Thm_PGLQuotient_summable_pi_geom
import Theorems.Thm_PGLQuotient_twWeight_cons_succ
import Theorems.Thm_PGLQuotient_twWeight_cons_zero
import Theorems.Thm_PGLQuotient_twWeight_le_vertexWeight
import Theorems.Thm_PGLQuotient_twWeight_pos
import Theorems.Thm_PGLQuotient_vertexWeight_le

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


/-- The majorant `q^{-P(g)}` of the vertex mass is summable over the dominant sector. -/
lemma summable_inv_pow_pairExp (hq : 1 < q) (n : ℕ) :
    Summable (fun g : Vertex (n + 1) => (q ^ pairExp g)⁻¹) := by
  have hlt : ∀ k : Fin (n + 1 - 1), gapRatio q (n + 1) 0 k < 1 := by
    intro k
    rcases n with _ | m
    · exact k.elim0
    · exact gapRatio_lt_one hq (by omega) (by exact_mod_cast Nat.succ_pos (m + 1)) k
  obtain ⟨hsum, -⟩ := summable_pi_geom (gapRatio q (n + 1) 0) (gapRatio_nonneg hq 0) hlt
  refine hsum.congr (fun g => ?_)
  rw [prod_gapRatio 0 g]
  simp

/-- The twisted vertex mass is summable over the whole quotient. -/
lemma summable_twWeight (hq : 1 < q) (n c j : ℕ) :
    Summable (fun g : Vertex (n + 1) => twWeight q c j g) := by
  refine Summable.of_nonneg_of_le (fun g => (twWeight_pos hq c j g).le) (fun g => ?_)
    ((summable_inv_pow_pairExp hq n).mul_left (((1 - q⁻¹) ^ (n + 1))⁻¹))
  exact le_trans (twWeight_le_vertexWeight hq c j g) (vertexWeight_le g hq)













open PGLQuotient in
theorem solution(hq : 1 < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 2), twWeight q c j g
      = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ *
        (∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g
          + (q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set K : ℝ := (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ with hKdef
  set M1 : ℝ := ∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g with hM1
  set M0 : ℝ := ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g with hM0
  have hKval : K = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ := by
    rw [hKdef]
    congr 1
    have h1 : q ^ (n + 2 + j) = q ^ (n + 1) * q ^ (1 + j) := by
      rw [← pow_add]; congr 1; omega
    have h2 : q ^ (1 + j) = q ^ (j + 1) := by rw [Nat.add_comm]
    rw [h1, inv_pow, h2]
    field_simp
  -- reindex the sum over the top gap
  have hsum2 : Summable (fun g : Vertex (n + 2) => twWeight q c j g) :=
    summable_twWeight hq (n + 1) c j
  have hF : Summable (fun p : ℕ × Vertex (n + 1) => twWeight q c j (consV p.1 p.2)) :=
    (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mpr hsum2
  have hreindex : ∑' g : Vertex (n + 2), twWeight q c j g
      = ∑' p : ℕ × Vertex (n + 1), twWeight q c j (consV p.1 p.2) :=
    ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq
      (fun g : Vertex (n + 2) => twWeight q c j g)).symm
  -- the two branches
  have hzero : ∑' g : Vertex (n + 1), twWeight q c j (consV 0 g) = K * M1 := by
    rw [tsum_congr (fun g => twWeight_cons_zero hq c j g), tsum_mul_left]
  have hsucc : ∀ a : ℕ, ∑' g : Vertex (n + 1), twWeight q c j (consV (a + 1) g)
      = K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0 := by
    intro a
    rw [tsum_congr (fun g => twWeight_cons_succ hq c j a g), tsum_mul_left]
  -- the geometric series in the top gap
  have hr0 : (0:ℝ) ≤ (q ^ ((n + 1) * (c + 1)))⁻¹ := by positivity
  have hrlt : (q ^ ((n + 1) * (c + 1)))⁻¹ < 1 := by
    have h1 : (1:ℝ) < q ^ ((n + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    rw [inv_lt_one_iff₀]
    right; exact h1
  have hgeom : ∑' a : ℕ, K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0
      = K * ((q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * M0) := by
    have hterm : ∀ a : ℕ, K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0
        = (K * M0 * (q ^ ((n + 1) * (c + 1)))⁻¹) * ((q ^ ((n + 1) * (c + 1)))⁻¹) ^ a := by
      intro a
      rw [← inv_pow, pow_succ]
      ring
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hrlt]
    have hx : (1:ℝ) < q ^ ((n + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    have hxpos : (0:ℝ) < q ^ ((n + 1) * (c + 1)) := by positivity
    field_simp
  rw [hreindex, hF.tsum_prod' (fun a => hF.prod_factor a), Summable.tsum_eq_zero_add hF.prod,
    hzero, tsum_congr hsucc, hgeom, ← hKval]
  ring
