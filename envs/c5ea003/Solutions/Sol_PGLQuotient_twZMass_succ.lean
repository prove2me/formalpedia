-- Prove2me | solution 1 for PGLQuotient.twZMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:43:03.548362+00:00
-- url     : https://prove2.me/submissions/a2469090-788e-4654-b8d6-37bc6ed9467c

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapAt_consV_succ
import Theorems.Thm_PGLQuotient_gapAt_consV_zero
import Theorems.Thm_PGLQuotient_summable_twZ
import Theorems.Thm_PGLQuotient_twWeight_cons_succ
import Theorems.Thm_PGLQuotient_twWeight_cons_zero

/-!
# The height zeta function in arbitrary rank: rationality and the pole at `s = d`

`Algebra.PGLQuotient.HeightZetaRankTwo` computes the positive-moment height zeta function

`Z_d(s) = ∑_λ α(λ)^s / |Aut λ|`

of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in closed form for `d = 2`,
exhibiting it as a rational function of `u = q^{s/2}` with a single pole at `u = q`.
This file establishes the corresponding statement in **arbitrary rank `d ≥ 1`**.

The mechanism is the same row-peeling recursion that produced the vertex volume in
`Algebra.PGLQuotient.VertexVolumeGeneral`, run on a *height-weighted* twisted mass

`twZ q c j w λ = w ^ heightExp λ · twWeight q c j λ`.

Since `heightExp (cons a λ') = (n+1)·a + heightExp λ'`, the extra factor is compatible with
peeling: it only changes the ratio of the geometric series in the top gap from
`q^{-(n+1)(c+1)}` to `w^{n+1} q^{-(n+1)(c+1)}`.  Hence:

* `twZMass_succ` — the row-peeling recursion for the height-weighted twisted mass;
* `twZ_rational` — for every rank and every pair of twisting parameters the sum is a rational
  function of `w` on the whole interval `0 ≤ w < q`, with a denominator that does not vanish
  there;
* `heightZeta_rational_general` — **the height zeta function of the rank-`d` quotient is a
  rational function of `u = q^{s/d}`**, uniformly for `s < d`;
* `heightZeta_unbounded_general` — **the pole at `s = d` is genuine in every rank**:
  `Z_d(s) → ∞` as `s ↑ d`.  Combined with `summable_weight_height_iff` this pins the abscissa
  of convergence at exactly `s = d`.

The threshold `w < q` is exactly `s < d` under `w = q^{s/d}`, so the domain of rationality is
precisely the half-plane of convergence.
-/

open PGLQuotient

open Finset

variable {q : ℝ}




variable {d : ℕ}






/-- The height weight is compatible with peeling the top row. -/
lemma heightExp_cons {n : ℕ} (a : ℕ) (g : Vertex (n + 1)) :
    heightExp (consV a g) = (n + 1) * a + heightExp g := by
  show ∑ k ∈ range (n + 1), (n + 1 - k) * gapAt (consV a g) k
      = (n + 1) * a + ∑ k ∈ range n, (n - k) * gapAt g k
  rw [Finset.sum_range_succ' (fun k => (n + 1 - k) * gapAt (consV a g) k) n,
    gapAt_consV_zero, Nat.sub_zero, Nat.add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [gapAt_consV_succ]
  congr 1
  omega

variable {w : ℝ}

lemma twZ_cons_zero {n : ℕ} (hq : 1 < q) (c j : ℕ) (g : Vertex (n + 1)) :
    twZ q c j w (consV 0 g)
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ * twZ q (c + 1) (j + 1) w g := by
  unfold twZ
  rw [heightExp_cons, twWeight_cons_zero hq, Nat.mul_zero, Nat.zero_add]
  ring

lemma twZ_cons_succ {n : ℕ} (hq : 1 < q) (c j a : ℕ) (g : Vertex (n + 1)) :
    twZ q c j w (consV (a + 1) g)
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹
        * ((w ^ (n + 1)) ^ (a + 1) * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹)
        * twZ q (c + 1) 0 w g := by
  unfold twZ
  rw [heightExp_cons, twWeight_cons_succ hq, pow_add, pow_mul]
  ring





open Polynomial








open PGLQuotient in
theorem solution(hq : 1 < q) (hw : 0 ≤ w) (hwq : w < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 2), twZ q c j w g
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ *
        (∑' g : Vertex (n + 1), twZ q (c + 1) (j + 1) w g
          + (w ^ (n + 1) / (q ^ ((n + 1) * (c + 1)) - w ^ (n + 1)))
              * ∑' g : Vertex (n + 1), twZ q (c + 1) 0 w g) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set K : ℝ := (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ with hKdef
  set A : ℝ := q ^ ((n + 1) * (c + 1)) with hA
  set W : ℝ := w ^ (n + 1) with hW
  set M1 : ℝ := ∑' g : Vertex (n + 1), twZ q (c + 1) (j + 1) w g with hM1
  set M0 : ℝ := ∑' g : Vertex (n + 1), twZ q (c + 1) 0 w g with hM0
  have hApos : (0:ℝ) < A := by rw [hA]; positivity
  have hWnn : (0:ℝ) ≤ W := by rw [hW]; positivity
  have hWA : W < A := by
    rw [hW, hA]
    calc w ^ (n + 1) < q ^ (n + 1) := pow_lt_pow_left₀ hwq hw (by omega)
      _ ≤ q ^ ((n + 1) * (c + 1)) :=
          pow_le_pow_right₀ hq.le (Nat.le_mul_of_pos_right _ (Nat.succ_pos c))
  set r : ℝ := W * A⁻¹ with hr
  have hr0 : (0:ℝ) ≤ r := by rw [hr]; positivity
  have hrlt : r < 1 := by
    rw [hr, ← div_eq_mul_inv, div_lt_one hApos]
    exact hWA
  -- reindex the sum over the top gap
  have hsum2 : Summable (fun g : Vertex (n + 2) => twZ q c j w g) :=
    summable_twZ hq hw hwq (n + 1) c j
  have hF : Summable (fun p : ℕ × Vertex (n + 1) => twZ q c j w (consV p.1 p.2)) :=
    (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mpr hsum2
  have hreindex : ∑' g : Vertex (n + 2), twZ q c j w g
      = ∑' p : ℕ × Vertex (n + 1), twZ q c j w (consV p.1 p.2) :=
    ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq
      (fun g : Vertex (n + 2) => twZ q c j w g)).symm
  have hzero : ∑' g : Vertex (n + 1), twZ q c j w (consV 0 g) = K * M1 := by
    rw [tsum_congr (fun g => twZ_cons_zero hq c j g), tsum_mul_left]
  have hsucc : ∀ a : ℕ, ∑' g : Vertex (n + 1), twZ q c j w (consV (a + 1) g)
      = K * (W ^ (a + 1) * ((A ^ (a + 1))⁻¹)) * M0 := by
    intro a
    rw [tsum_congr (fun g => twZ_cons_succ hq c j a g), tsum_mul_left]
  have hgeom : ∑' a : ℕ, K * (W ^ (a + 1) * ((A ^ (a + 1))⁻¹)) * M0
      = K * ((W / (A - W)) * M0) := by
    have hterm : ∀ a : ℕ, K * (W ^ (a + 1) * ((A ^ (a + 1))⁻¹)) * M0
        = (K * M0 * r) * r ^ a := by
      intro a
      simp only [hr, mul_pow, inv_pow, pow_succ, mul_inv]
      ring
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hrlt]
    have hAne : A ≠ 0 := ne_of_gt hApos
    have hAW : A - W ≠ 0 := by
      have : (0:ℝ) < A - W := by linarith
      exact ne_of_gt this
    have h1r : (1 : ℝ) - r ≠ 0 := by
      have : (0:ℝ) < 1 - r := by linarith
      exact ne_of_gt this
    rw [hr]
    field_simp
  rw [hreindex, hF.tsum_prod' (fun a => hF.prod_factor a), Summable.tsum_eq_zero_add hF.prod,
    hzero, tsum_congr hsucc, hgeom]
  ring
