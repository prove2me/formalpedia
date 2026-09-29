-- Prove2me | Definitions.Def_KServer_race_var3
-- name    : KServer_race_var3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T21:28:02.905585+00:00
-- url     : https://prove2.me/theorems/cc1c2692-e55d-406d-b4f0-deff4f596ef5
-- title:
--   Sharp race variance via block independence
-- statement:
--   The head, coin/survivor, and closing blocks of the race total are independent under the race measure, so their variances add exactly. The middle block equals the surviving side's total up to a pathwise (kappa+1) c_B correction, so its variance is at most 2V plus lower-order terms. The resulting bound on the variance of the race total is V_A + 2V + 2V_C plus terms of order (kappa c_B)^2 and c_B^2 — linear in the carried variances rather than quadratic in the side masses, which is what the level recursion of the lower-bound construction needs to close.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Var3

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- A chunk system's sample space is nonempty (its measure sums to one). -/
theorem omega_nonempty (C : ChunkSystemB X s t 0 cB T pe mL) :
    Nonempty C.Ω := by
  rcases isEmpty_or_nonempty C.Ω with hE | hN
  · exfalso
    have h := C.hPsum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact zero_ne_one h
  · exact hN

/-- The coin weights do not depend on the head outcome. -/
theorem coinW_indep (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) :
    coinW A BL BR a l r (ε := ε) = coinW A BL BR a' l r (ε := ε) := rfl

/-- Expected absolute deviation is controlled by the second moment
(Cauchy–Schwarz). -/
theorem sum_abs_le_sqrt {ι : Type*} [Fintype ι] (P Y : ι → ℝ) {W : ℝ}
    (hP : ∀ i, 0 ≤ P i) (hs : ∑ i, P i = 1)
    (hV : ∑ i, P i * Y i ^ 2 ≤ W) :
    ∑ i, P i * |Y i| ≤ Real.sqrt W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (P i)) (fun i => Real.sqrt (P i) * |Y i|)
  have he1 : ∀ i, Real.sqrt (P i) * (Real.sqrt (P i) * |Y i|)
      = P i * |Y i| := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (hP i)]
  have he2 : ∀ i, Real.sqrt (P i) ^ 2 = P i := fun i => Real.sq_sqrt (hP i)
  have he3 : ∀ i, (Real.sqrt (P i) * |Y i|) ^ 2 = P i * Y i ^ 2 := by
    intro i
    rw [mul_pow, Real.sq_sqrt (hP i), sq_abs]
  rw [Finset.sum_congr rfl fun i _ => he1 i,
    Finset.sum_congr rfl fun i _ => he2 i,
    Finset.sum_congr rfl fun i _ => he3 i, hs, one_mul] at hcs
  have hnn : 0 ≤ ∑ i, P i * |Y i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hP i) (abs_nonneg _)
  have h2 : (∑ i, P i * |Y i|) ^ 2 ≤ W := le_trans hcs hV
  calc ∑ i, P i * |Y i|
      = Real.sqrt ((∑ i, P i * |Y i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt W := Real.sqrt_le_sqrt h2

/-- A partial sum of sizes is at most the count times the ceiling. -/
theorem preSum_le_mul (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (hcB : 0 ≤ cB) (n : ℕ) : preSum C ωc n ≤ (n : ℝ) * cB := by
  unfold preSum
  refine le_trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) =>
    sizeN_le_cB C hcB i ωc) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Cross-expectation of a head function against a coin/side function
vanishes when the head factor is centered. -/
theorem RP_cross_zero_A (hε : 0 < ε) (f : A.Ω → ℝ)
    (g : RΩ A BL BR CC κ → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc', χ))
    (hf0 : ∑ a : A.Ω, A.P a * f a = 0) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * (f ω.1 * g ω) = 0 := by
  obtain ⟨a₀⟩ := omega_nonempty A
  obtain ⟨c₀⟩ := omega_nonempty CC
  set K : ℝ := ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
    BL.P l * (BR.P r * (CC.P cc
      * coinWt (coinW A BL BR a₀ l r (ε := ε)) c))
      * g (a₀, l, r, c₀, c) with hK
  have hslice : ∀ a : A.Ω,
      (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c)
          * (f (a, l, r, cc, c).1 * g (a, l, r, cc, c)))
      = A.P a * f a * K := by
    intro a
    rw [hK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun cc _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hg a a₀ l r cc c₀ c]
    show A.P a * (BL.P l * (BR.P r * (CC.P cc
        * coinWt (coinW A BL BR a l r (ε := ε)) c)))
        * (f a * g (a₀, l, r, c₀, c)) = _
    rw [coinW_indep A BL BR ε a a₀ l r]
    ring
  rw [sum_RΩ_expand]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => hslice a) ?_
  rw [← Finset.sum_mul, hf0, zero_mul]

/-- Cross-expectation of a head function against a closing function
factorizes; it vanishes when the head factor is centered. -/
theorem RP_cross_zero_AC (hε : 0 < ε) (f : A.Ω → ℝ) (h : CC.Ω → ℝ)
    (hf0 : ∑ a : A.Ω, A.P a * f a = 0) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (f ω.1 * h ω.2.2.2.1) = 0 := by
  have hcc : ∀ a : A.Ω, ∀ l : BL.Ω, ∀ r : BR.Ω,
      (∑ cc : CC.Ω, A.P a * BL.P l * BR.P r * CC.P cc * (f a * h cc))
      = A.P a * BL.P l * BR.P r * f a
        * (∑ cc : CC.Ω, CC.P cc * h cc) := by
    intro a l r
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun cc _ => by ring
  have hr : ∀ a : A.Ω, ∀ l : BL.Ω,
      (∑ r : BR.Ω, A.P a * BL.P l * BR.P r * f a
        * (∑ cc : CC.Ω, CC.P cc * h cc))
      = A.P a * BL.P l * f a * (∑ cc : CC.Ω, CC.P cc * h cc) := by
    intro a l
    exact sum_P_mul BR.P BR.hPsum
      (A.P a * BL.P l * f a * (∑ cc : CC.Ω, CC.P cc * h cc))
      _ (fun r => by ring)
  have hl : ∀ a : A.Ω,
      (∑ l : BL.Ω, A.P a * BL.P l * f a
        * (∑ cc : CC.Ω, CC.P cc * h cc))
      = A.P a * f a * (∑ cc : CC.Ω, CC.P cc * h cc) := by
    intro a
    exact sum_P_mul BL.P BL.hPsum
      (A.P a * f a * (∑ cc : CC.Ω, CC.P cc * h cc)) _ (fun l => by ring)
  calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (f ω.1 * h ω.2.2.2.1)
      = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          A.P a * BL.P l * BR.P r * CC.P cc * (f a * h cc) :=
        RP_marg A BL BR CC κ ε hε (fun a _ _ cc => f a * h cc)
    _ = ∑ a : A.Ω, A.P a * f a * (∑ cc : CC.Ω, CC.P cc * h cc) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
          Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hcc a l r,
          Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hr a l,
          hl a]
    _ = (∑ a : A.Ω, A.P a * f a) * (∑ cc : CC.Ω, CC.P cc * h cc) :=
        (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hf0, zero_mul]

/-- Cross-expectation of a coin/side function against a closing function
vanishes when the closing factor is centered. -/
theorem RP_cross_zero_C (hε : 0 < ε)
    (g : RΩ A BL BR CC κ → ℝ) (h : CC.Ω → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc', χ))
    (hh0 : ∑ cc : CC.Ω, CC.P cc * h cc = 0) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (g ω * h ω.2.2.2.1) = 0 := by
  obtain ⟨a₀⟩ := omega_nonempty A
  obtain ⟨c₀⟩ := omega_nonempty CC
  have hpt : ∀ (a : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (c : Fin κ → Bool),
      RP A BL BR CC κ ε (a, l, r, cc, c)
        * (g (a, l, r, cc, c) * h cc)
      = (CC.P cc * h cc)
        * (A.P a * BL.P l * BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) c
            * g (a₀, l, r, c₀, c)) := by
    intro a l r cc c
    rw [hg a a₀ l r cc c₀ c]
    show A.P a * (BL.P l * (BR.P r * (CC.P cc
        * coinWt (coinW A BL BR a l r (ε := ε)) c)))
        * (g (a₀, l, r, c₀, c) * h cc) = _
    rw [coinW_indep A BL BR ε a a₀ l r]
    ring
  have hslice : ∀ (a : A.Ω) (l : BL.Ω) (r : BR.Ω),
      (∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c)
          * (g (a, l, r, cc, c) * h cc)) = 0 := by
    intro a l r
    calc ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
          RP A BL BR CC κ ε (a, l, r, cc, c)
            * (g (a, l, r, cc, c) * h cc)
        = ∑ cc : CC.Ω, ∑ c : Fin κ → Bool, (CC.P cc * h cc)
            * (A.P a * BL.P l * BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c
                * g (a₀, l, r, c₀, c)) :=
          Finset.sum_congr rfl fun cc _ =>
            Finset.sum_congr rfl fun c _ => hpt a l r cc c
      _ = ∑ cc : CC.Ω, (CC.P cc * h cc)
            * ∑ c : Fin κ → Bool, A.P a * BL.P l * BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c
                * g (a₀, l, r, c₀, c) :=
          Finset.sum_congr rfl fun cc _ => (Finset.mul_sum _ _ _).symm
      _ = (∑ cc : CC.Ω, CC.P cc * h cc)
            * ∑ c : Fin κ → Bool, A.P a * BL.P l * BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c
                * g (a₀, l, r, c₀, c) :=
          (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hh0, zero_mul]
  calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (g ω * h ω.2.2.2.1)
      = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          ∑ c : Fin κ → Bool, RP A BL BR CC κ ε (a, l, r, cc, c)
            * (g (a, l, r, cc, c) * h cc) :=
        sum_RΩ_expand A BL BR CC κ
          (fun ω => RP A BL BR CC κ ε ω * (g ω * h ω.2.2.2.1))
    _ = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, (0 : ℝ) :=
        Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun l _ =>
            Finset.sum_congr rfl fun r _ => hslice a l r
    _ = 0 := by simp

/-- The middle (coin/survivor) block of the race total. -/
noncomputable def gBlock (ω : RΩ A BL BR CC κ) : ℝ :=
  (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
    + survPart A BL BR CC κ ω

/-- The middle block depends only on the side and coin outcomes. -/
theorem gBlock_congr (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
    (χ : Fin κ → Bool) :
    gBlock A BL BR CC κ ε (a, l, r, cc, χ)
      = gBlock A BL BR CC κ ε (a', l, r, cc', χ) := rfl

/-- The total of the surviving side. -/
noncomputable def selTot (ω : RΩ A BL BR CC κ) : ℝ :=
  if survL A BL BR CC κ ω then preSum BL ω.2.1 BL.m
  else preSum BR ω.2.2.1 BR.m

/-- The middle block differs from the surviving-side total by at most
`(κ+1)·c_B`: the coin terms add at most `κ·c_B` and the consumed prefix
subtracts at most `(κ+1)·c_B`. -/
theorem gBlock_sub_selTot (hε : 0 < ε) (hcB : 0 ≤ cB)
    (ω : RΩ A BL BR CC κ) :
    |gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω|
      ≤ ((κ : ℝ) + 1) * cB := by
  have hc0 : 0 ≤ ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j :=
    Finset.sum_nonneg fun j _ => coinTerm_nonneg A BL BR CC κ ε hε ω j
  have hcK : ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
      ≤ (κ : ℝ) * cB := by
    refine le_trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.range κ) =>
      coinTerm_le_cB A BL BR CC κ ε hε hcB ω j) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases Bool.eq_false_or_eq_true (survL A BL BR CC κ ω) with hs | hs
  · -- left side survives
    have hρ0 : 0 ≤ preSum BL ω.2.1 (cntL ω.2.2.2.2 κ + 1) :=
      preSum_nonneg BL ω.2.1 _
    have hρK : preSum BL ω.2.1 (cntL ω.2.2.2.2 κ + 1)
        ≤ ((κ : ℝ) + 1) * cB := by
      refine le_trans (preSum_le_mul BL ω.2.1 hcB _) ?_
      have h1 : cntL ω.2.2.2.2 κ ≤ κ := cntL_le ω.2.2.2.2 (le_refl κ)
      have h2 : ((cntL ω.2.2.2.2 κ + 1 : ℕ) : ℝ) ≤ (κ : ℝ) + 1 := by
        push_cast
        have h3 : ((cntL ω.2.2.2.2 κ : ℕ) : ℝ) ≤ (κ : ℝ) :=
          Nat.cast_le.mpr h1
        linarith
      exact mul_le_mul_of_nonneg_right h2 hcB
    have hval : gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω
        = (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
          - preSum BL ω.2.1 (cntL ω.2.2.2.2 κ + 1) := by
      unfold gBlock selTot survPart
      rw [if_pos hs, if_pos hs]
      ring
    rw [hval]
    rw [abs_le]
    constructor
    · have hκ1 : (κ : ℝ) * cB ≤ ((κ : ℝ) + 1) * cB :=
        mul_le_mul_of_nonneg_right (by linarith) hcB
      linarith
    · have hκ1 : (κ : ℝ) * cB ≤ ((κ : ℝ) + 1) * cB :=
        mul_le_mul_of_nonneg_right (by linarith) hcB
      linarith
  · -- right side survives
    have hρ0 : 0 ≤ preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1) :=
      preSum_nonneg BR ω.2.2.1 _
    have hρK : preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1)
        ≤ ((κ : ℝ) + 1) * cB := by
      refine le_trans (preSum_le_mul BR ω.2.2.1 hcB _) ?_
      have h1 : cntR ω.2.2.2.2 κ ≤ κ := cntR_le ω.2.2.2.2 (le_refl κ)
      have h2 : ((cntR ω.2.2.2.2 κ + 1 : ℕ) : ℝ) ≤ (κ : ℝ) + 1 := by
        push_cast
        have h3 : ((cntR ω.2.2.2.2 κ : ℕ) : ℝ) ≤ (κ : ℝ) :=
          Nat.cast_le.mpr h1
        linarith
      exact mul_le_mul_of_nonneg_right h2 hcB
    have hval : gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω
        = (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
          - preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1) := by
      unfold gBlock selTot survPart
      rw [if_neg (by simp [hs]), if_neg (by simp [hs])]
      ring
    rw [hval]
    rw [abs_le]
    constructor
    · have hκ1 : (κ : ℝ) * cB ≤ ((κ : ℝ) + 1) * cB :=
        mul_le_mul_of_nonneg_right (by linarith) hcB
      linarith
    · have hκ1 : (κ : ℝ) * cB ≤ ((κ : ℝ) + 1) * cB :=
        mul_le_mul_of_nonneg_right (by linarith) hcB
      linarith

open Classical in
/-- **The race variance, sharp form.**  The head, coin/survivor, and
closing blocks of the race total are independent under the race measure,
so their variances add exactly.  The middle block equals the surviving
side's total up to a pathwise `(κ+1)·c_B` correction, so its variance is
at most `2V` plus lower-order terms — linear in the carried variances
rather than quadratic in the side masses. -/
theorem race_var3 (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {VA V VC : ℝ}
    (hmean : ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i
      = ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i)
    (hVarA : ∑ a : A.Ω, A.P a * ((∑ i, A.size a i)
        - ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i) ^ 2 ≤ VA)
    (hVarL : ∑ l : BL.Ω, BL.P l * ((∑ i, BL.size l i)
        - ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i) ^ 2 ≤ V)
    (hVarR : ∑ r : BR.Ω, BR.P r * ((∑ i, BR.size r i)
        - ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i) ^ 2 ≤ V)
    (hVarC : ∑ cc : CC.Ω, CC.P cc * ((∑ i, CC.size cc i)
        - ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i) ^ 2 ≤ VC) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω (i : ℕ))
          - ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
              * ∑ i : Fin (mrace A BL BR CC κ),
                  rsize A BL BR CC κ ε ω' (i : ℕ)) ^ 2
      ≤ VA + (2 * V + 2 * (((κ : ℝ) + 1) * cB) * Real.sqrt (2 * V)
          + (((κ : ℝ) + 1) * cB) ^ 2)
        + (2 * VC + 2 * cB ^ 2) := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  set mA := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * preSum A ω.1 A.m with hmA
  set mG := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * gBlock A BL BR CC κ ε ω with hmG
  set mC := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * ccPart A BL BR CC κ ω with hmC
  have hmeantot : ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω' (i : ℕ)
      = mA + mG + mC := by
    rw [hmA, hmG, hmC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    unfold gBlock
    ring
  rw [hmeantot]
  -- centering identities
  have hf0 : ∑ a : A.Ω, A.P a * (preSum A a A.m - mA) = 0 := by
    have h1 : mA = ∑ a : A.Ω, A.P a * preSum A a A.m := by
      rw [hmA]
      exact RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [sum_mul_sub A.P (fun a => preSum A a A.m) (fun _ => mA),
      sum_P_mul A.P A.hPsum mA (fun a => A.P a * mA) (fun a => by ring),
      ← h1, sub_self]
  have hh0 : ∑ cc : CC.Ω, CC.P cc
      * ((preSum CC cc CC.m - preSum CC cc 1) - mC) = 0 := by
    have h1 : mC = ∑ cc : CC.Ω, CC.P cc
        * (preSum CC cc CC.m - preSum CC cc 1) := by
      rw [hmC]
      exact RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    rw [sum_mul_sub CC.P
        (fun cc => preSum CC cc CC.m - preSum CC cc 1) (fun _ => mC),
      sum_P_mul CC.P CC.hPsum mC (fun cc => CC.P cc * mC)
        (fun cc => by ring),
      ← h1, sub_self]
  have hgcong : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
      (χ : Fin κ → Bool),
      gBlock A BL BR CC κ ε (a, l, r, cc, χ) - mG
        = gBlock A BL BR CC κ ε (a', l, r, cc', χ) - mG := by
    intro a a' l r cc cc' χ
    rw [gBlock_congr A BL BR CC κ ε a a' l r cc cc' χ]
  -- vanishing cross terms
  have hPQ : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((preSum A ω.1 A.m - mA)
        * (gBlock A BL BR CC κ ε ω - mG)) = 0 :=
    RP_cross_zero_A A BL BR CC κ ε hε
      (fun a => preSum A a A.m - mA)
      (fun ω => gBlock A BL BR CC κ ε ω - mG) hgcong hf0
  have hPR : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((preSum A ω.1 A.m - mA)
        * (ccPart A BL BR CC κ ω - mC)) = 0 :=
    RP_cross_zero_AC A BL BR CC κ ε hε
      (fun a => preSum A a A.m - mA)
      (fun cc => (preSum CC cc CC.m - preSum CC cc 1) - mC) hf0
  have hQR : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((gBlock A BL BR CC κ ε ω - mG)
        * (ccPart A BL BR CC κ ω - mC)) = 0 :=
    RP_cross_zero_C A BL BR CC κ ε hε
      (fun ω => gBlock A BL BR CC κ ε ω - mG)
      (fun cc => (preSum CC cc CC.m - preSum CC cc 1) - mC) hgcong hh0
  -- head block
  have hEA : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (preSum A ω.1 A.m - mA) ^ 2 ≤ VA := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (preSum A ω.1 A.m - mA) ^ 2
        = ∑ a : A.Ω, A.P a * (preSum A a A.m - mA) ^ 2 :=
      RP_margA A BL BR CC κ ε hε (fun a => (preSum A a A.m - mA) ^ 2)
    have hmeanA : ∑ a' : A.Ω, A.P a' * preSum A a' A.m
        = ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i :=
      Finset.sum_congr rfl fun a' _ => by rw [preSum_total]
    have h2 : mA = ∑ a' : A.Ω, A.P a' * preSum A a' A.m := by
      rw [hmA]
      exact RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [h1]
    refine le_trans (le_of_eq ?_) hVarA
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [preSum_total, h2, hmeanA]
  -- closing block
  have hEC : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (ccPart A BL BR CC κ ω - mC) ^ 2 ≤ 2 * VC + 2 * cB ^ 2 := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (ccPart A BL BR CC κ ω - mC) ^ 2
        = ∑ cc : CC.Ω, CC.P cc
            * ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2 :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2)
    have h2a : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ccPart A BL BR CC κ ω
        = ∑ cc : CC.Ω, CC.P cc
            * (preSum CC cc CC.m - preSum CC cc 1) :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    have h2 : mC = (∑ cc : CC.Ω, CC.P cc * preSum CC cc CC.m)
        - ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 := by
      rw [hmC, h2a, sum_mul_sub]
    have hp0 : ∀ cc : CC.Ω, 0 ≤ preSum CC cc 1 :=
      fun cc => preSum_nonneg CC cc 1
    have hpB : ∀ cc : CC.Ω, preSum CC cc 1 ≤ cB := by
      intro cc
      have h5 : preSum CC cc 1 = CC.sizeN 0 cc := by
        unfold preSum
        rw [Finset.sum_range_one]
      rw [h5]
      exact sizeN_le_cB CC hcB 0 cc
    have hμ0 : 0 ≤ ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 :=
      Finset.sum_nonneg fun cc _ => mul_nonneg (CC.hP cc).le (hp0 cc)
    have hμB : ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 ≤ cB := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left (hpB cc) (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum cB (fun cc => CC.P cc * cB)
        (fun cc => by ring)
    have hb1 : ∀ cc : CC.Ω,
        ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2
          ≤ 2 * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
            + 2 * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 := by
      intro cc
      rw [h2]
      nlinarith [sq_nonneg ((preSum CC cc CC.m
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m)
        + (preSum CC cc 1
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1))]
    rw [h1]
    refine le_trans (Finset.sum_le_sum fun cc _ =>
      mul_le_mul_of_nonneg_left (hb1 cc) (CC.hP cc).le) ?_
    have hsplit2 : ∑ cc : CC.Ω, CC.P cc
        * (2 * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
          + 2 * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
        = 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
          + 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2) := by
      rw [Finset.sum_congr rfl (fun cc _ =>
        show CC.P cc
            * (2 * (preSum CC cc CC.m
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
              + 2 * (preSum CC cc 1
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          = 2 * (CC.P cc * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
            + 2 * (CC.P cc * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          from by ring),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsplit2]
    have hmeanC : ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m
        = ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i :=
      Finset.sum_congr rfl fun cc' _ => by rw [preSum_total]
    have hVt : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2 ≤ VC := by
      refine le_trans (le_of_eq ?_) hVarC
      refine Finset.sum_congr rfl fun cc _ => ?_
      rw [preSum_total, hmeanC]
    have hVp : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 ≤ cB ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left
          (sq_le_sq' (b := cB) (by linarith [hp0 cc, hμB])
            (by linarith [hpB cc, hμ0]))
          (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum (cB ^ 2)
        (fun cc => CC.P cc * cB ^ 2) (fun cc => by ring)
    linarith
  -- middle block
  have hEG : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (gBlock A BL BR CC κ ε ω - mG) ^ 2
      ≤ 2 * V + 2 * (((κ : ℝ) + 1) * cB) * Real.sqrt (2 * V)
        + (((κ : ℝ) + 1) * cB) ^ 2 := by
    set μ := ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i with hμ
    -- E[(sel-μ)²] ≤ 2V
    have hpath2 : ∀ ω : RΩ A BL BR CC κ,
        (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ (preSum BL ω.2.1 BL.m - μ) ^ 2
            + (preSum BR ω.2.2.1 BR.m - μ) ^ 2 := by
      intro ω
      unfold selTot
      split
      · nlinarith [sq_nonneg (preSum BR ω.2.2.1 BR.m - μ)]
      · nlinarith [sq_nonneg (preSum BL ω.2.1 BL.m - μ)]
    have hL : ∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2 ≤ V := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
        hVarL
      rw [preSum_total]
    have hR : ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 ≤ V := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
        hVarR
      rw [preSum_total, hmean]
    have hsel2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (selTot A BL BR CC κ ω - μ) ^ 2 ≤ 2 * V := by
      have h5 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * ((preSum BL ω.2.1 BL.m - μ) ^ 2
                + (preSum BR ω.2.2.1 BR.m - μ) ^ 2) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hpath2 ω) (hRP0 ω)
      have h6 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ((preSum BL ω.2.1 BL.m - μ) ^ 2
            + (preSum BR ω.2.2.1 BR.m - μ) ^ 2)
          = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2) :=
        RP_margLR A BL BR CC κ ε hε
          (fun l r => (preSum BL l BL.m - μ) ^ 2
            + (preSum BR r BR.m - μ) ^ 2)
      have hrow : ∀ l : BL.Ω,
          ∑ r : BR.Ω, BL.P l * BR.P r
            * ((preSum BL l BL.m - μ) ^ 2
              + (preSum BR r BR.m - μ) ^ 2)
          = BL.P l * (preSum BL l BL.m - μ) ^ 2
            + BL.P l * (∑ r : BR.Ω, BR.P r
                * (preSum BR r BR.m - μ) ^ 2) := by
        intro l
        rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) =>
          show BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2)
            = BL.P l * (preSum BL l BL.m - μ) ^ 2 * BR.P r
              + BL.P l * (BR.P r * (preSum BR r BR.m - μ) ^ 2)
            from by ring),
          Finset.sum_add_distrib]
        congr 1
        · exact sum_P_mul BR.P BR.hPsum
            (BL.P l * (preSum BL l BL.m - μ) ^ 2) _ (fun r => by ring)
        · rw [Finset.mul_sum]
      have h7 : ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
          * ((preSum BL l BL.m - μ) ^ 2 + (preSum BR r BR.m - μ) ^ 2)
          = (∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2)
            + ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 := by
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hrow l,
          Finset.sum_add_distrib]
        congr 1
        exact sum_P_mul BL.P BL.hPsum
          (∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2) _
          (fun l => by ring)
      calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * ((preSum BL ω.2.1 BL.m - μ) ^ 2
                + (preSum BR ω.2.2.1 BR.m - μ) ^ 2) := h5
        _ = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2) := h6
        _ = (∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2)
              + ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 := h7
        _ ≤ 2 * V := by linarith
    -- shift the center from μ to the true mean
    have hz : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - mG) = 0 := by
      rw [sum_mul_sub (RP A BL BR CC κ ε)
          (fun ω => gBlock A BL BR CC κ ε ω) (fun _ => mG),
        sum_P_mul (RP A BL BR CC κ ε) hRPs mG
          (fun ω => RP A BL BR CC κ ε ω * mG) (fun ω => by ring),
        ← hmG, sub_self]
    have hshift : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - mG) ^ 2
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (gBlock A BL BR CC κ ε ω - μ) ^ 2 := by
      have hiden : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (gBlock A BL BR CC κ ε ω - μ) ^ 2
          = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (gBlock A BL BR CC κ ε ω - mG) ^ 2)
            + (mG - μ) ^ 2 := by
        rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ) =>
          show RP A BL BR CC κ ε ω * (gBlock A BL BR CC κ ε ω - μ) ^ 2
            = RP A BL BR CC κ ε ω
                * (gBlock A BL BR CC κ ε ω - mG) ^ 2
              + 2 * (mG - μ) * (RP A BL BR CC κ ε ω
                  * (gBlock A BL BR CC κ ε ω - mG))
              + (mG - μ) ^ 2 * RP A BL BR CC κ ε ω
            from by ring),
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, hz, mul_zero, add_zero, ← Finset.mul_sum,
          hRPs, mul_one]
      linarith [sq_nonneg (mG - μ)]
    refine le_trans hshift ?_
    -- pathwise bound about μ
    have hpath : ∀ ω : RΩ A BL BR CC κ,
        (gBlock A BL BR CC κ ε ω - μ) ^ 2
          ≤ (selTot A BL BR CC κ ω - μ) ^ 2
            + 2 * (((κ : ℝ) + 1) * cB) * |selTot A BL BR CC κ ω - μ|
            + (((κ : ℝ) + 1) * cB) ^ 2 := by
      intro ω
      have hd := gBlock_sub_selTot A BL BR CC κ ε hε hcB ω
      have h1 : gBlock A BL BR CC κ ε ω - μ
          = (selTot A BL BR CC κ ω - μ)
            + (gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω) := by
        ring
      have h3 : 2 * (selTot A BL BR CC κ ω - μ)
          * (gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω)
          ≤ 2 * (((κ : ℝ) + 1) * cB) * |selTot A BL BR CC κ ω - μ| := by
        calc 2 * (selTot A BL BR CC κ ω - μ)
              * (gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω)
            ≤ |2 * (selTot A BL BR CC κ ω - μ)
                * (gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω)| :=
              le_abs_self _
          _ = 2 * |selTot A BL BR CC κ ω - μ|
                * |gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω| := by
              rw [abs_mul, abs_mul, abs_two]
          _ ≤ 2 * |selTot A BL BR CC κ ω - μ| * (((κ : ℝ) + 1) * cB) :=
              mul_le_mul_of_nonneg_left hd (by positivity)
          _ = 2 * (((κ : ℝ) + 1) * cB)
                * |selTot A BL BR CC κ ω - μ| := by ring
      have h4 : (gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω) ^ 2
          ≤ (((κ : ℝ) + 1) * cB) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      nlinarith [h3, h4, sq_nonneg (selTot A BL BR CC κ ω - μ)]
    have hsum1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - μ) ^ 2
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ((selTot A BL BR CC κ ω - μ) ^ 2
              + 2 * (((κ : ℝ) + 1) * cB) * |selTot A BL BR CC κ ω - μ|
              + (((κ : ℝ) + 1) * cB) ^ 2) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hpath ω) (hRP0 ω)
    refine le_trans hsum1 ?_
    have hsplit : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((selTot A BL BR CC κ ω - μ) ^ 2
          + 2 * (((κ : ℝ) + 1) * cB) * |selTot A BL BR CC κ ω - μ|
          + (((κ : ℝ) + 1) * cB) ^ 2)
        = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (selTot A BL BR CC κ ω - μ) ^ 2)
          + 2 * (((κ : ℝ) + 1) * cB)
            * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
                * |selTot A BL BR CC κ ω - μ|)
          + (((κ : ℝ) + 1) * cB) ^ 2 := by
      rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ) =>
        show RP A BL BR CC κ ε ω
            * ((selTot A BL BR CC κ ω - μ) ^ 2
              + 2 * (((κ : ℝ) + 1) * cB) * |selTot A BL BR CC κ ω - μ|
              + (((κ : ℝ) + 1) * cB) ^ 2)
          = RP A BL BR CC κ ε ω * (selTot A BL BR CC κ ω - μ) ^ 2
            + 2 * (((κ : ℝ) + 1) * cB) * (RP A BL BR CC κ ε ω
                * |selTot A BL BR CC κ ω - μ|)
            + (((κ : ℝ) + 1) * cB) ^ 2 * RP A BL BR CC κ ε ω
          from by ring),
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hRPs, mul_one]
    rw [hsplit]
    have habs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |selTot A BL BR CC κ ω - μ| ≤ Real.sqrt (2 * V) :=
      sum_abs_le_sqrt (RP A BL BR CC κ ε)
        (fun ω => selTot A BL BR CC κ ω - μ) hRP0 hRPs hsel2
    have hc1 : (0 : ℝ) ≤ 2 * (((κ : ℝ) + 1) * cB) := by positivity
    have hmul := mul_le_mul_of_nonneg_left habs hc1
    linarith
  -- assemble
  have hexpand : ∀ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((∑ i : Fin (mrace A BL BR CC κ),
            rsize A BL BR CC κ ε ω (i : ℕ)) - (mA + mG + mC)) ^ 2
      = RP A BL BR CC κ ε ω * (preSum A ω.1 A.m - mA) ^ 2
        + RP A BL BR CC κ ε ω * (gBlock A BL BR CC κ ε ω - mG) ^ 2
        + RP A BL BR CC κ ε ω * (ccPart A BL BR CC κ ω - mC) ^ 2
        + 2 * (RP A BL BR CC κ ε ω * ((preSum A ω.1 A.m - mA)
            * (gBlock A BL BR CC κ ε ω - mG)))
        + 2 * (RP A BL BR CC κ ε ω * ((preSum A ω.1 A.m - mA)
            * (ccPart A BL BR CC κ ω - mC)))
        + 2 * (RP A BL BR CC κ ε ω * ((gBlock A BL BR CC κ ε ω - mG)
            * (ccPart A BL BR CC κ ω - mC))) := by
    intro ω
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    unfold gBlock
    ring
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hexpand ω,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hPQ, hPR, hQR]
  linarith [hEA, hEG, hEC]

end Var3

end Race

end KServer


