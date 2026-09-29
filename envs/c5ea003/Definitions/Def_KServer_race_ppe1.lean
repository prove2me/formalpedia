-- Prove2me | Definitions.Def_KServer_race_ppe1
-- name    : KServer_race_ppe1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T00:33:47.307073+00:00
-- url     : https://prove2.me/theorems/9538fb47-8558-4ce2-ba3b-d5581b3fbd63
-- title:
--   Race prophecy energy: the head phase is exact
-- statement:
--   Head-phase prophecy energy of the race. Defines the race tail masses rtailN (the sum of race sizes from an output position to the end) and the raw race conditional expectation rcond over rhist2 atoms. Race sizes and tails beyond the head phase never read the head outcome (definitional). A race tail with an in-head end decomposes as the head system's tail plus the head-independent middle-and-continuation block. The race conditional of a head function plus a head-independent function over a head-phase atom splits as the head conditional plus the constant full expectation (race_cond_split, via the restricted marginalization lemmas). Consequently the head-phase Doob increments of a race tail with an in-head end EQUAL the head system's Doob increments of the corresponding head tail (race_dinc_head_in), and those of a beyond-head tail VANISH (race_dinc_head_out); the per-depth prophecy terms marginalize exactly to the head system's terms (race_ppe_head_term, race_ppe_head_term_out). This is the first third of the race prophecy-energy propagation: at head-phase depths the race creates no new prophecy.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: race prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_race_sel
import Definitions.Def_KServer_race_sturdyout
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section PPE1

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The race tail mass from output position `e`. -/
noncomputable def rtailN (e : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  ∑ r ∈ Finset.Ico e (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω r

/-- The race conditional expectation over `rhist2` atoms, raw form. -/
noncomputable def rcond (f : RΩ A BL BR CC κ → ℝ) (n : ℕ)
    (ω : RΩ A BL BR CC κ) : ℝ :=
  (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
    RP A BL BR CC κ ε ω' * f ω')
  / (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
    RP A BL BR CC κ ε ω')

/-- Race sizes beyond the head never read the head outcome. -/
theorem rsize_fst_indep {i : ℕ} (hi : A.m ≤ i)
    (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω) (χ : Fin κ → Bool) :
    rsize A BL BR CC κ ε (a, l, r, cc, χ) i
      = rsize A BL BR CC κ ε (a', l, r, cc, χ) i := by
  unfold rsize
  conv_lhs => rw [if_neg (show ¬ i < A.m by omega)]
  conv_rhs => rw [if_neg (show ¬ i < A.m by omega)]
  by_cases hik : i < A.m + κ
  · conv_lhs => rw [if_pos hik]
    conv_rhs => rw [if_pos hik]
    rfl
  · conv_lhs => rw [if_neg hik]
    conv_rhs => rw [if_neg hik]
    have hrc : remCnt A BL BR CC κ (a, l, r, cc, χ)
        = remCnt A BL BR CC κ (a', l, r, cc, χ) := rfl
    have hsv : survL A BL BR CC κ (a, l, r, cc, χ)
        = survL A BL BR CC κ (a', l, r, cc, χ) := rfl
    rw [hrc, hsv]

/-- Race tails from head-or-later positions never read the head
outcome. -/
theorem rtail_fst_indep {e : ℕ} (he : A.m ≤ e)
    (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω) (χ : Fin κ → Bool) :
    rtailN A BL BR CC κ ε e (a, l, r, cc, χ)
      = rtailN A BL BR CC κ ε e (a', l, r, cc, χ) := by
  unfold rtailN
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  exact rsize_fst_indep A BL BR CC κ ε (by omega) a a' l r cc χ

/-- Race tails with in-head ends decompose into a head tail plus the
head-independent block. -/
theorem rtail_head_decomp (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {e : ℕ} (he : e ≤ A.m) (ω : RΩ A BL BR CC κ) :
    rtailN A BL BR CC κ ε e ω
      = (∑ i ∈ Finset.Ico e A.m, A.sizeN i ω.1)
        + (gBlock A BL BR CC κ ε ω + ccPart A BL BR CC κ ω) := by
  have hfull := rsum_decomp A BL BR CC κ ε hκL hκR ω
  rw [Fin.sum_univ_eq_sum_range
    (fun i => rsize A BL BR CC κ ε ω i) _] at hfull
  have hAm : A.m ≤ mrace A BL BR CC κ := by
    unfold mrace
    omega
  have hprefix : ∑ r ∈ Finset.range e, rsize A BL BR CC κ ε ω r
      = ∑ i ∈ Finset.range e, A.sizeN i ω.1 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    unfold rsize
    rw [if_pos (by omega)]
  have hsplit : (∑ r ∈ Finset.range e, rsize A BL BR CC κ ε ω r)
      + rtailN A BL BR CC κ ε e ω
      = ∑ r ∈ Finset.range (mrace A BL BR CC κ),
          rsize A BL BR CC κ ε ω r := by
    unfold rtailN
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le e) (by omega)
  have hpre2 : (∑ i ∈ Finset.range e, A.sizeN i ω.1)
      + ∑ i ∈ Finset.Ico e A.m, A.sizeN i ω.1
      = preSum A ω.1 A.m := by
    unfold preSum
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le e) he
  have hgb : gBlock A BL BR CC κ ε ω
      = (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
        + survPart A BL BR CC κ ω := rfl
  linarith [hfull, hsplit, hprefix, hpre2, hgb]

open Classical in
/-- **Race conditionals at head depths split**: the conditional of a
head function plus a head-independent function over a head-phase atom
is the head conditional plus the constant full expectation. -/
theorem race_cond_split (hε : 0 < ε) {n : ℕ} (hn : n ≤ A.m)
    (F : A.Ω → ℝ) (G : RΩ A BL BR CC κ → ℝ)
    (hG : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (χ : Fin κ → Bool), G (a, l, r, cc, χ) = G (a', l, r, cc, χ))
    (ω : RΩ A BL BR CC κ) :
    rcond A BL BR CC κ ε (fun ω' => F ω'.1 + G ω') n ω
      = A.condExp F n ω.1
        + ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω' * G ω' := by
  unfold rcond
  rw [race_atom_A A BL BR CC κ hn ω]
  have hSfst : Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      A.hist n ω'.1 = A.hist n ω.1)
      = Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        ω'.1 ∈ A.atom n ω.1) := by
    ext ω'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ChunkSystemB.mem_atom]
  rw [hSfst]
  have hnum : ∑ ω' ∈ Finset.univ.filter
      (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1),
      RP A BL BR CC κ ε ω' * (F ω'.1 + G ω')
      = (∑ a ∈ A.atom n ω.1, A.P a * F a)
        + (∑ a ∈ A.atom n ω.1, A.P a)
          * ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω' * G ω' := by
    rw [Finset.sum_congr rfl fun ω' _ =>
      show RP A BL BR CC κ ε ω' * (F ω'.1 + G ω')
        = RP A BL BR CC κ ε ω' * F ω'.1 + RP A BL BR CC κ ε ω' * G ω'
      from by ring, Finset.sum_add_distrib]
    congr 1
    · exact RP_restrict_margA A BL BR CC κ ε hε (A.atom n ω.1) F
    · exact RP_restrict_rest A BL BR CC κ ε hε (A.atom n ω.1) G hG
  have hden : ∑ ω' ∈ Finset.univ.filter
      (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1),
      RP A BL BR CC κ ε ω'
      = ∑ a ∈ A.atom n ω.1, A.P a := by
    have h1 := RP_restrict_margA A BL BR CC κ ε hε (A.atom n ω.1)
      (fun _ => (1 : ℝ))
    rw [Finset.sum_congr rfl fun ω' _ =>
      (mul_one (RP A BL BR CC κ ε ω')).symm, h1]
    exact Finset.sum_congr rfl fun a _ => mul_one (A.P a)
  rw [hnum, hden]
  have hmass : (0 : ℝ) < ∑ a ∈ A.atom n ω.1, A.P a :=
    A.mass_atom_pos n ω.1
  rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hmass)]
  rfl

/-- Head-phase increments of an in-head race tail are the head system's
increments of the corresponding head tail. -/
theorem race_dinc_head_in (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {h e : ℕ} (hh : h + 1 ≤ A.m) (he : e ≤ A.m) (ω : RΩ A BL BR CC κ) :
    rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) (h + 1) ω
      - rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) h ω
    = A.dinc (fun a => ∑ i ∈ Finset.Ico e A.m, A.sizeN i a) h ω.1 := by
  have hre : ∀ n ≤ A.m, rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n ω
      = A.condExp (fun a => ∑ i ∈ Finset.Ico e A.m, A.sizeN i a) n ω.1
        + ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
            * (gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω') := by
    intro n hn
    have h1 : rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n ω
        = rcond A BL BR CC κ ε (fun ω' =>
            (∑ i ∈ Finset.Ico e A.m, A.sizeN i ω'.1)
            + (gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω')) n ω := by
      unfold rcond
      congr 1
      refine Finset.sum_congr rfl fun ω' _ => ?_
      rw [rtail_head_decomp A BL BR CC κ ε hκL hκR he ω']
    rw [h1]
    exact race_cond_split A BL BR CC κ ε hε hn
      (fun a => ∑ i ∈ Finset.Ico e A.m, A.sizeN i a)
      (fun ω' => gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω')
      (fun a a' l r cc χ => by
        show gBlock A BL BR CC κ ε (a, l, r, cc, χ)
            + ccPart A BL BR CC κ (a, l, r, cc, χ)
          = gBlock A BL BR CC κ ε (a', l, r, cc, χ)
            + ccPart A BL BR CC κ (a', l, r, cc, χ)
        rw [gBlock_congr A BL BR CC κ ε a a' l r cc cc χ]
        rfl) ω
  rw [hre (h + 1) hh, hre h (by omega)]
  unfold ChunkSystemB.dinc
  ring

/-- Head-phase increments of a beyond-head race tail vanish. -/
theorem race_dinc_head_out (hε : 0 < ε)
    {h e : ℕ} (hh : h + 1 ≤ A.m) (he : A.m ≤ e) (ω : RΩ A BL BR CC κ) :
    rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) (h + 1) ω
      - rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) h ω = 0 := by
  have hre : ∀ n ≤ A.m, rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n ω
      = ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
          * rtailN A BL BR CC κ ε e ω' := by
    intro n hn
    have h1 : rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n ω
        = rcond A BL BR CC κ ε (fun ω' =>
            (fun _ : A.Ω => (0 : ℝ)) ω'.1
              + rtailN A BL BR CC κ ε e ω') n ω := by
      unfold rcond
      congr 1
      refine Finset.sum_congr rfl fun ω' _ => ?_
      show RP A BL BR CC κ ε ω' * rtailN A BL BR CC κ ε e ω'
        = RP A BL BR CC κ ε ω' * (0 + rtailN A BL BR CC κ ε e ω')
      ring
    rw [h1, race_cond_split A BL BR CC κ ε hε hn
      (fun _ => (0 : ℝ)) (rtailN A BL BR CC κ ε e)
      (fun a a' l r cc χ => rtail_fst_indep A BL BR CC κ ε he a a' l r cc χ)
      ω]
    rw [A.condExp_const 0 n ω.1, zero_add]
  rw [hre (h + 1) hh, hre h (by omega), sub_self]

/-- The head-phase prophecy terms of the race equal the head system's:
in-head cell ends. -/
theorem race_ppe_head_term (hε : 0 < ε) (hκL : κ ≤ BL.m)
    (hκR : κ ≤ BR.m) {h e : ℕ} (hh : h + 1 ≤ A.m) (he : e ≤ A.m) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) (h + 1) ω
        - rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) h ω) ^ 2
    = ∑ a : A.Ω, A.P a
        * (A.dinc (fun a' => ∑ i ∈ Finset.Ico e A.m, A.sizeN i a') h a) ^ 2 := by
  rw [Finset.sum_congr rfl fun ω _ => by
    rw [race_dinc_head_in A BL BR CC κ ε hε hκL hκR hh he ω]]
  exact RP_margA A BL BR CC κ ε hε
    (fun a => (A.dinc (fun a' =>
      ∑ i ∈ Finset.Ico e A.m, A.sizeN i a') h a) ^ 2)

/-- The head-phase prophecy terms of the race vanish for beyond-head
cell ends. -/
theorem race_ppe_head_term_out (hε : 0 < ε)
    {h e : ℕ} (hh : h + 1 ≤ A.m) (he : A.m ≤ e) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) (h + 1) ω
        - rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) h ω) ^ 2
    = 0 := by
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [race_dinc_head_out A BL BR CC κ ε hε hh he ω]
  norm_num

/-- The head tail matches the head system's `tailSum`. -/
theorem head_tail_eq (e : ℕ) (a : A.Ω) :
    (∑ i ∈ Finset.Ico e A.m, A.sizeN i a) = A.tailSum e a := rfl

end PPE1

end Race

end KServer


