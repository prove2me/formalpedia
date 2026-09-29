-- Prove2me | solution 1 for quadratic_neumann_correction_lambda_sample_bound_from_general_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T19:56:31.401855+00:00
-- url     : https://prove2.me/submissions/2ea9e471-d251-433e-b128-2704ce723d3c

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Local validation of node 21c1297a
`quadratic_neumann_correction_lambda_sample_bound_from_general_bound`.

Claim (verified TRUE this session): the cardinality constraint `m ≤ n₁ n₂`
together with the general-bound density hypothesis forces the quadratic-Neumann
density bound, PROVIDED the existential constant `C` is chosen large enough
(depending on `C₂`).  This reverses the session-11 suspicion that it was false.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Real

/-- Helper: for `a ≥ 0`, `(a^(1/4))^4 = a`. -/
theorem rpow_quarter_pow_four {a : ℝ} (ha : 0 ≤ a) :
    (a ^ ((1:ℝ)/4)) ^ (4:ℕ) = a := by
  rw [← Real.rpow_natCast (a ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul ha]
  norm_num

/-- Helper: `a^(4/3) = a * a^(1/3)` for `a ≥ 0`. -/
theorem rpow_four_thirds {a : ℝ} (ha : 0 ≤ a) :
    a ^ ((4:ℝ)/3) = a * a ^ ((1:ℝ)/3) := by
  rw [show (4:ℝ)/3 = 1 + 1/3 by norm_num]
  rw [Real.rpow_add_of_nonneg ha (by norm_num) (by norm_num), Real.rpow_one]

/-- For `a ≥ 0`: `a = (a^(1/3))^3`. -/
theorem cube_rpow_third {a : ℝ} (ha : 0 ≤ a) : (a ^ ((1:ℝ)/3)) ^ (3:ℕ) = a := by
  rw [← Real.rpow_natCast (a ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul ha]; norm_num

set_option maxHeartbeats 1600000 in
/-- The main node, full statement. -/
theorem node_21c1297a (C₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          max 1 ((8 * C₂) ^ 2) * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) := by
  set lam : ℝ := max 1 ((8 * C₂) ^ 2) with hlam
  have hlam1 : (1:ℝ) ≤ lam := le_max_left _ _
  have hlam0 : (0:ℝ) < lam := lt_of_lt_of_le one_pos hlam1
  -- Choose C = (lam^3 / (2 log 2))^{1/4}, but a cleaner sufficient C: any C with C^4*(2 log 2) ≥ lam^3.
  refine ⟨(lam ^ 3 / (2 * Real.log 2)) ^ ((1:ℝ)/4) + 1, ?_, ?_⟩
  · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbase : 0 ≤ lam ^ 3 / (2 * Real.log 2) := by positivity
    have : 0 ≤ (lam ^ 3 / (2 * Real.log 2)) ^ ((1:ℝ)/4) :=
      Real.rpow_nonneg hbase _
    linarith
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hcard hμ₀ hμ₁ hA0 hA1 hLHS
  -- abbreviations
  set n : ℕ := max n₁ n₂ with hn
  have hnR : (1:ℝ) ≤ (n:ℝ) := by
    have : 1 ≤ n := le_trans hn₁ (le_max_left _ _)
    exact_mod_cast this
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  -- case n = 1
  by_cases hn1 : (n:ℝ) = 1
  · -- log n = 0, RHS = 0, m ≥ 0
    have hlog0 : Real.log (n:ℝ) = 0 := by rw [hn1]; exact Real.log_one
    rw [hlog0]
    have : max 1 ((8 * C₂) ^ 2) * Real.rpow μ₀ ((4 : ℝ) / 3) * (↑(max n₁ n₂)) *
        Real.rpow (r : ℝ) ((4 : ℝ) / 3) * (β * 0) = 0 := by ring
    rw [show (↑(max n₁ n₂):ℝ) = (n:ℝ) from rfl] at *
    simp only [mul_zero, mul_zero]
    positivity
  -- case n ≥ 2 region: n > 1
  · have hngt1 : (1:ℝ) < (n:ℝ) := lt_of_le_of_ne hnR (Ne.symm hn1)
    have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos hngt1
    have hβ0 : (0:ℝ) < β := by linarith
    set P : ℝ := β * Real.log (n:ℝ) with hP
    have hP0 : 0 < P := by rw [hP]; positivity
    -- substitution variables
    set q : ℝ := μ₀ ^ ((1:ℝ)/3) with hq
    set s : ℝ := (r:ℝ) ^ ((1:ℝ)/3) with hs
    set t : ℝ := (n:ℝ) ^ ((1:ℝ)/4) with ht
    have hq0 : 0 < q := Real.rpow_pos_of_pos hμ₀0 _
    have hs0 : 0 < s := Real.rpow_pos_of_pos (by exact_mod_cast hr) _
    have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith) _
    have hμ0cube : μ₀ = q ^ (3:ℕ) := (cube_rpow_third (le_of_lt hμ₀0)).symm
    have hrcube : (r:ℝ) = s ^ (3:ℕ) := (cube_rpow_third (by exact_mod_cast Nat.zero_le r)).symm
    have hnquart : (n:ℝ) = t ^ (4:ℕ) := (rpow_quarter_pow_four (by linarith)).symm
    -- μ₀^(4/3) = (μ₀^(1/3))^4 = q^4
    have hμ43 : Real.rpow μ₀ ((4:ℝ)/3) = q ^ (4:ℕ) := by
      have : μ₀ ^ ((4:ℝ)/3) = (μ₀ ^ ((1:ℝ)/3)) ^ (4:ℕ) := by
        rw [← Real.rpow_natCast (μ₀ ^ ((1:ℝ)/3)) 4, ← Real.rpow_mul (le_of_lt hμ₀0)]
        norm_num
      rw [show Real.rpow μ₀ ((4:ℝ)/3) = μ₀ ^ ((4:ℝ)/3) from rfl, this, ← hq]
    have hr43 : Real.rpow (r:ℝ) ((4:ℝ)/3) = s ^ (4:ℕ) := by
      have hrnn : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.zero_le r
      have : (r:ℝ) ^ ((4:ℝ)/3) = ((r:ℝ) ^ ((1:ℝ)/3)) ^ (4:ℕ) := by
        rw [← Real.rpow_natCast ((r:ℝ) ^ ((1:ℝ)/3)) 4, ← Real.rpow_mul hrnn]
        norm_num
      rw [show Real.rpow (r:ℝ) ((4:ℝ)/3) = (r:ℝ) ^ ((4:ℝ)/3) from rfl, this, ← hs]
    -- the MAX ≥ μ₀ * n^{1/4} = q^3 * t
    have hquart : Real.rpow (↑(max n₁ n₂)) ((1:ℝ)/4) = t := rfl
    have hMAXge : max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) ≥ μ₀ * t := by
      rw [hquart] at *
      exact le_max_right _ _
    -- LHS lower bound by the n^{1/4} branch
    have hLHS2 : (m:ℝ) ≥ C' * (μ₀ * t) * (n:ℝ) * (r:ℝ) * P := by
      refine le_trans ?_ hLHS
      have hC'0 : 0 < C' := lt_of_lt_of_le (by positivity) hC'
      rw [show (↑(max n₁ n₂):ℝ) = (n:ℝ) from rfl] at *
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      have hnpos : (0:ℝ) < (n:ℝ) := by linarith
      have hfac : (0:ℝ) ≤ C' * (n:ℝ) * (r:ℝ) * P := by positivity
      nlinarith [hMAXge, mul_le_mul_of_nonneg_left hMAXge (le_of_lt hC'0),
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC'0) (le_of_lt hnpos)) (le_of_lt hrpos)) (le_of_lt hP0)]
    -- cardinality m ≤ n^2
    have hcardR : (m:ℝ) ≤ (n:ℝ) ^ (2:ℕ) := by
      have h1 : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hcard
      have h2 : (n₁:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have h3 : (n₂:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_max_right n₁ n₂
      have : (n₁:ℝ) * (n₂:ℝ) ≤ (n:ℝ) * (n:ℝ) :=
        mul_le_mul h2 h3 (by positivity) (by linarith)
      calc (m:ℝ) ≤ (n₁:ℝ)*(n₂:ℝ) := h1
        _ ≤ (n:ℝ)*(n:ℝ) := this
        _ = (n:ℝ)^(2:ℕ) := by ring
    have hC'0 : 0 < C' := lt_of_lt_of_le (by positivity) hC'
    -- Convert to q,s,t. n = t^4, r = s^3, μ₀ = q^3.
    -- LHS2: m ≥ C' * (q^3 * t) * t^4 * s^3 * P  = C' * t^5 * q^3 * s^3 * P
    rw [hμ0cube, hrcube, hnquart] at hLHS2
    rw [hnquart] at hcardR
    -- card: m ≤ (t^4)^2 = t^8
    -- derive (q s)^3 bound:  C' t^5 q^3 s^3 P ≤ m ≤ t^8
    have hcard2 : C' * (q ^ (3:ℕ) * t) * (t ^ (4:ℕ)) * (s ^ (3:ℕ)) * P ≤ (t ^ (4:ℕ)) ^ (2:ℕ) := by
      exact le_trans hLHS2 hcardR
    -- key: C' t ≥ lam q s, via cube + C'^4 P ≥ lam^3
    -- First C^4 * (2 log2) ≥ lam^3 for the chosen C, and C' ≥ C, P ≥ 2 log 2 actually P>2 log2
    have hn2nat : 2 ≤ n := by
      have h1n : 1 < n := by exact_mod_cast hngt1
      omega
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2nat
    have hPge : P ≥ 2 * Real.log 2 := by
      have hlog2le : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn2
      rw [hP]
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [hlog2le, hl2, le_of_lt hβ0, hβ]
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- C chosen: C = (lam^3/(2 log2))^{1/4} + 1
    set Cval : ℝ := (lam ^ 3 / (2 * Real.log 2)) ^ ((1:ℝ)/4) + 1 with hCval
    have hC4 : lam ^ 3 ≤ Cval ^ (4:ℕ) * (2 * Real.log 2) := by
      have hbase : 0 ≤ lam ^ 3 / (2 * Real.log 2) := by positivity
      have hbq : ((lam ^ 3 / (2 * Real.log 2)) ^ ((1:ℝ)/4)) ^ (4:ℕ)
          = lam ^ 3 / (2 * Real.log 2) := rpow_quarter_pow_four hbase
      have hge : (lam ^ 3 / (2 * Real.log 2)) ≤ Cval ^ (4:ℕ) := by
        rw [hCval]
        set b : ℝ := (lam ^ 3 / (2 * Real.log 2)) ^ ((1:ℝ)/4) with hb
        have h0 : 0 ≤ b := Real.rpow_nonneg hbase _
        have hbq' : b ^ (4:ℕ) = lam ^ 3 / (2 * Real.log 2) := hbq
        have hmono : b ^ (4:ℕ) ≤ (b + 1) ^ (4:ℕ) :=
          pow_le_pow_left₀ h0 (by linarith) 4
        rw [← hbq']; exact hmono
      have h2log0 : 0 < 2 * Real.log 2 := by positivity
      calc lam ^ 3 = (lam ^ 3 / (2 * Real.log 2)) * (2 * Real.log 2) := by
              field_simp
        _ ≤ Cval ^ (4:ℕ) * (2 * Real.log 2) := by
              apply mul_le_mul_of_nonneg_right hge (le_of_lt h2log0)
    -- C' ≥ Cval ⇒ C'^4 ≥ Cval^4 ; and P ≥ 2 log2 ⇒ C'^4 * P ≥ Cval^4 * 2 log2 ≥ lam^3
    have hC'4P : lam ^ 3 ≤ C' ^ (4:ℕ) * P := by
      have hC'geC : Cval ≤ C' := hC'
      have hCvalpos : 0 < Cval := by rw [hCval]; positivity
      have h1 : Cval ^ (4:ℕ) ≤ C' ^ (4:ℕ) := by
        apply pow_le_pow_left₀ (le_of_lt hCvalpos) hC'geC
      calc lam ^ 3 ≤ Cval ^ (4:ℕ) * (2 * Real.log 2) := hC4
        _ ≤ C' ^ (4:ℕ) * (2 * Real.log 2) := by
            apply mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ C' ^ (4:ℕ) * P := by
            apply mul_le_mul_of_nonneg_left hPge (by positivity)
    -- now: (qs)^3 ≤ t^3 / (C' P)  from hcard2 (divide t^4 ... )
    -- goal in q,s,t,P form
    rw [hμ43, hr43, hnquart]
    -- target: m ≥ lam * q^4 * t^4 * s^4 * P
    -- have m ≥ C' t^5 q^3 s^3 P (hLHS2)
    -- suffices C' t^5 q^3 s^3 P ≥ lam q^4 t^4 s^4 P, i.e. C' t ≥ lam q s
    have hkey : C' * t ≥ lam * (q * s) := by
      -- cube: (C' t)^3 ≥ (lam q s)^3 ⟺ C'^3 t^3 ≥ lam^3 q^3 s^3
      -- from card: C' t^5 q^3 s^3 P ≤ t^8 ⟹ q^3 s^3 ≤ t^3/(C' P)
      have hcard3 : q ^ (3:ℕ) * s ^ (3:ℕ) ≤ t ^ (3:ℕ) / (C' * P) := by
        have hCP : 0 < C' * P := by positivity
        rw [le_div_iff₀ hCP]
        -- goal: q^3 s^3 * (C' P) ≤ t^3.  From hcard2 (× t^5 both sides cancel).
        have ht5pos : 0 < t ^ (5:ℕ) := by positivity
        -- hcard2 : C'*(q^3*t)*t^4*s^3*P ≤ (t^4)^2.  rewrite both as multiples of t^5
        have hL : C' * (q ^ (3:ℕ) * t) * (t ^ (4:ℕ)) * (s ^ (3:ℕ)) * P
            = (q ^ (3:ℕ) * s ^ (3:ℕ) * (C' * P)) * t ^ (5:ℕ) := by ring
        have hR : (t ^ (4:ℕ)) ^ (2:ℕ) = (t ^ (3:ℕ)) * t ^ (5:ℕ) := by ring
        rw [hL, hR] at hcard2
        exact le_of_mul_le_mul_right hcard2 ht5pos
      -- so lam^3 q^3 s^3 ≤ lam^3 t^3/(C' P) ≤ C'^4 P t^3/(C' P) = C'^3 t^3
      have hcube : (lam * (q * s)) ^ (3:ℕ) ≤ (C' * t) ^ (3:ℕ) := by
        have e1 : (lam * (q * s)) ^ (3:ℕ) = lam ^ (3:ℕ) * (q ^ (3:ℕ) * s ^ (3:ℕ)) := by ring
        have e2 : (C' * t) ^ (3:ℕ) = C' ^ (3:ℕ) * t ^ (3:ℕ) := by ring
        rw [e1, e2]
        have hlam3 : lam ^ (3:ℕ) = lam ^ 3 := by norm_num
        have step1 : lam ^ (3:ℕ) * (q ^ (3:ℕ) * s ^ (3:ℕ))
            ≤ lam ^ (3:ℕ) * (t ^ (3:ℕ) / (C' * P)) := by
          apply mul_le_mul_of_nonneg_left hcard3 (by positivity)
        have step2 : lam ^ (3:ℕ) * (t ^ (3:ℕ) / (C' * P)) ≤ C' ^ (3:ℕ) * t ^ (3:ℕ) := by
          have hCP : 0 < C' * P := by positivity
          have heq : lam ^ (3:ℕ) * (t ^ (3:ℕ) / (C' * P))
              = (lam ^ (3:ℕ) * t ^ (3:ℕ)) / (C' * P) := by ring
          rw [heq, div_le_iff₀ hCP, hlam3]
          have ht3 : 0 ≤ t ^ (3:ℕ) := by positivity
          have hb : lam ^ 3 ≤ C' ^ (4:ℕ) * P := hC'4P
          nlinarith [hb, ht3, mul_pos hC'0 hP0, hC'0, hP0]
        exact le_trans step1 step2
      -- take cube roots: both sides nonneg
      have hnn2 : 0 ≤ C' * t := by positivity
      exact le_of_pow_le_pow_left₀ (by norm_num) hnn2 hcube
    -- finish: m ≥ C' t^5 q^3 s^3 P ≥ lam q^4 t^4 s^4 P
    have hfinal : lam * q ^ (4:ℕ) * (t ^ (4:ℕ)) * s ^ (4:ℕ) * P
        ≤ C' * (q ^ (3:ℕ) * t) * (t ^ (4:ℕ)) * (s ^ (3:ℕ)) * P := by
      -- = (q^3 t^4 s^3 P) * (C' t)  vs  (q^3 t^4 s^3 P) * (lam q s)
      have hfac : 0 ≤ q ^ (3:ℕ) * (t ^ (4:ℕ)) * s ^ (3:ℕ) * P := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hfac, hq0, hs0, ht0, hP0]
    exact le_trans hfinal hLHS2

end MatrixCompletion

open MatrixCompletion

theorem solution (C₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          max 1 ((8 * C₂) ^ 2) * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) :=
  MatrixCompletion.node_21c1297a C₂
