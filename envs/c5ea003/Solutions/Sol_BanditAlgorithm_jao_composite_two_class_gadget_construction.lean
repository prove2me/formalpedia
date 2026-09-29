-- Prove2me | solution 1 for BanditAlgorithm.jao_composite_two_class_gadget_construction
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T15:04:46.221725+00:00
-- url     : https://prove2.me/submissions/a3dfd639-4665-4f30-bf8d-617fed33664b

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning
import Theorems.Thm_BanditAlgorithm_mdp_travel_time_le_of_lyapunov_drift

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoConstr

/-! ### The de Bruijn navigation graph on `ZMod c`

Digit alphabet `{0, …, k-1}`; the step `s ↦ s * k + j`.  If `c ≤ k ^ L` then
every state is reachable from every other in at most `L` steps, and the
distance function below decreases by one along a suitable digit. -/

section DeBruijn

variable {c k : ℕ} [NeZero c]

/-- `z` is reachable from `s` in `ℓ` de Bruijn steps iff the "missing digits"
residue `z - s k^ℓ` is smaller than `k^ℓ`. -/
def Reach (z s : ZMod c) (ℓ : ℕ) : Prop := (z - s * (k : ZMod c) ^ ℓ).val < k ^ ℓ

instance (z s : ZMod c) (ℓ : ℕ) : Decidable (Reach (k := k) z s ℓ) := by
  unfold Reach; infer_instance

lemma reach_of_le {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) : Reach (k := k) z s L :=
  lt_of_lt_of_le (ZMod.val_lt _) hL

/-- The de Bruijn distance from `s` to `z` (junk `0` when `c > k ^ L` for all
`L`, which cannot happen under the hypothesis we use). -/
noncomputable def dst (z s : ZMod c) : ℕ :=
  open Classical in
  if h : ∃ ℓ, Reach (k := k) z s ℓ then Nat.find h else 0

lemma dst_le {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) : dst (k := k) z s ≤ L := by
  have h : ∃ ℓ, Reach (k := k) z s ℓ := ⟨L, reach_of_le hL z s⟩
  classical
  rw [dst, dif_pos h]
  exact Nat.find_le (reach_of_le hL z s)

lemma reach_dst {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) :
    Reach (k := k) z s (dst (k := k) z s) := by
  have h : ∃ ℓ, Reach (k := k) z s ℓ := ⟨L, reach_of_le hL z s⟩
  classical
  rw [dst, dif_pos h]
  exact Nat.find_spec h

lemma dst_min {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) {ℓ : ℕ}
    (hlt : ℓ < dst (k := k) z s) : ¬ Reach (k := k) z s ℓ := by
  have h : ∃ ℓ, Reach (k := k) z s ℓ := ⟨L, reach_of_le hL z s⟩
  classical
  rw [dst, dif_pos h] at hlt
  exact Nat.find_min h hlt

lemma dst_le_of_reach {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) {ℓ : ℕ}
    (hr : Reach (k := k) z s ℓ) : dst (k := k) z s ≤ ℓ := by
  by_contra hc
  exact dst_min hL z s (by omega) hr

lemma dst_eq_zero_iff {L : ℕ} (hL : c ≤ k ^ L) (z s : ZMod c) :
    dst (k := k) z s = 0 ↔ s = z := by
  constructor
  · intro h0
    have := reach_dst hL z s
    rw [h0] at this
    simp only [Reach, pow_zero, mul_one] at this
    have hz : (z - s).val = 0 := by omega
    have h2 : z - s = 0 := (ZMod.val_eq_zero (z - s)).mp hz
    have : z = s := by linear_combination (norm := abel) h2
    exact this.symm
  · intro h
    subst h
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    refine dst_le_of_reach hL _ _ ?_
    simp only [Reach, pow_zero, mul_one, sub_self]
    simp

/-- The key step: from `s ≠ z` there is a digit `j < k` whose de Bruijn step
strictly decreases the distance to `z`. -/
lemma exists_digit {L : ℕ} (hL : c ≤ k ^ L) (hk : 0 < k) (z s : ZMod c) (hsz : s ≠ z) :
    ∃ j : ℕ, j < k ∧
      dst (k := k) z (s * (k : ZMod c) + (j : ZMod c)) < dst (k := k) z s := by
  classical
  set ℓ := dst (k := k) z s with hℓdef
  have hℓpos : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · exact absurd ((dst_eq_zero_iff hL z s).mp h) hsz
    · exact h
  have hspec : Reach (k := k) z s ℓ := reach_dst hL z s
  have hmin : ¬ Reach (k := k) z s (ℓ - 1) := dst_min hL z s (by omega)
  set m : ℕ := (z - s * (k : ZMod c) ^ ℓ).val with hmdef
  have hm : m < k ^ ℓ := hspec
  set b : ℕ := k ^ (ℓ - 1) with hbdef
  have hkb : k ^ ℓ = b * k := by
    rw [hbdef, ← pow_succ]
    congr 1
    omega
  refine ⟨m / b, ?_, ?_⟩
  · have hbpos : 0 < b := Nat.pow_pos hk
    have hmk : m < k * b := by rw [mul_comm, ← hkb]; exact hm
    exact (Nat.div_lt_iff_lt_mul hbpos).mpr hmk
  · -- the new residue is `m % b`
    have hbpos : 0 < b := Nat.pow_pos hk
    have hbc : b < c := by
      have hnr : ¬ ((z - s * (k : ZMod c) ^ (ℓ - 1)).val < b) := hmin
      have := ZMod.val_lt (z - s * (k : ZMod c) ^ (ℓ - 1))
      omega
    have hkey : z - (s * (k : ZMod c) + ((m / b : ℕ) : ZMod c)) * (k : ZMod c) ^ (ℓ - 1)
        = ((m % b : ℕ) : ZMod c) := by
      have h1 : ((m : ℕ) : ZMod c) = z - s * (k : ZMod c) ^ ℓ := by
        rw [hmdef]; simp
      have h2 : (k : ZMod c) ^ ℓ = (k : ZMod c) ^ (ℓ - 1) * (k : ZMod c) := by
        rw [← pow_succ]; congr 1; omega
      have h3 : (m : ℕ) = b * (m / b) + m % b := by
        rw [Nat.add_comm]; exact (Nat.mod_add_div m b).symm
      have h5 : ((b : ℕ) : ZMod c) = (k : ZMod c) ^ (ℓ - 1) := by
        rw [hbdef]; push_cast; ring
      have h4 : ((m : ℕ) : ZMod c)
          = (k : ZMod c) ^ (ℓ - 1) * ((m / b : ℕ) : ZMod c) + ((m % b : ℕ) : ZMod c) := by
        conv_lhs => rw [h3]
        push_cast
        rw [h5]
      calc z - (s * (k : ZMod c) + ((m / b : ℕ) : ZMod c)) * (k : ZMod c) ^ (ℓ - 1)
          = (z - s * (k : ZMod c) ^ ℓ)
              - (k : ZMod c) ^ (ℓ - 1) * ((m / b : ℕ) : ZMod c) := by
            rw [h2]; ring
        _ = ((m : ℕ) : ZMod c) - (k : ZMod c) ^ (ℓ - 1) * ((m / b : ℕ) : ZMod c) := by
            rw [h1]
        _ = ((m % b : ℕ) : ZMod c) := by rw [h4]; ring
    have hval : (z - (s * (k : ZMod c) + ((m / b : ℕ) : ZMod c)) * (k : ZMod c) ^ (ℓ - 1)).val
        = m % b := by
      rw [hkey, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hbpos) hbc)
    have hreach : Reach (k := k) z (s * (k : ZMod c) + ((m / b : ℕ) : ZMod c)) (ℓ - 1) := by
      unfold Reach
      rw [hval]
      exact lt_of_lt_of_le (Nat.mod_lt _ hbpos) (le_of_eq hbdef.symm)
    have := dst_le_of_reach hL z _ hreach
    omega

end DeBruijn

/-! ### The composite gadget

Class-0 states are `0, …, cls S - 1` with `cls S = ⌈S/2⌉`; class-1 states are
`cls S, …, S - 1` (there are `⌊S/2⌋ ≤ cls S` of them, so every class-1 state is
`up` of a class-0 state).  Actions `0, …, ⌊A/2⌋ - 1` are the *arm* actions (a
self-loop of `nav`), the remaining `⌈A/2⌉` are the *navigation* digits. -/

section Gadget

variable {S A : ℕ}

/-- The number of navigation (graph) states, `⌊S/2⌋`; also the number of
class-1 states. -/
abbrev nlo (S : ℕ) : ℕ := S / 2
/-- The number of class-0 states, `⌈S/2⌉`. -/
abbrev nhi (S : ℕ) : ℕ := (S + 1) / 2
/-- The number of arm actions, `⌊A/2⌋`. -/
abbrev arms (A : ℕ) : ℕ := A / 2
/-- The number of de Bruijn digits: one navigation action is reserved as the
escape edge onto the leftover class-0 state. -/
abbrev digs (A : ℕ) : ℕ := (A + 1) / 2 - 1

/-- `Fin n` element from a natural number, reduced mod `n`. -/
def fmk (n : ℕ) [NeZero n] (v : ℕ) : Fin n := ⟨v % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

lemma fmk_val {n : ℕ} [NeZero n] {v : ℕ} (h : v < n) : (fmk n v).val = v :=
  Nat.mod_eq_of_lt h

/-- A residue mod `nlo S`, viewed as a graph state. -/
def ofZ [NeZero (nlo S)] (x : ZMod (nlo S)) : Fin S :=
  ⟨x.val, by have h := ZMod.val_lt x; simp only [nlo] at h; omega⟩

/-- The residue of a state mod `nlo S`. -/
def toZ [NeZero (nlo S)] (s : Fin S) : ZMod (nlo S) := (s.val : ZMod (nlo S))

lemma ofZ_val [NeZero (nlo S)] (x : ZMod (nlo S)) : (ofZ (S := S) x).val = x.val := rfl

lemma toZ_ofZ [NeZero (nlo S)] (x : ZMod (nlo S)) : toZ (ofZ (S := S) x) = x := by
  rw [toZ, ofZ_val, ZMod.natCast_val, ZMod.cast_id]

lemma ofZ_toZ [NeZero (nlo S)] {s : Fin S} (h : s.val < nlo S) : ofZ (toZ s) = s := by
  apply Fin.ext
  rw [ofZ_val, toZ, ZMod.val_natCast_of_lt h]

lemma ofZ_lt [NeZero (nlo S)] (x : ZMod (nlo S)) : (ofZ (S := S) x).val < nlo S := by
  rw [ofZ_val]; exact ZMod.val_lt x

/-- The leftover class-0 state (only genuinely extra when `S` is odd). -/
def xtra (S : ℕ) [NeZero S] : Fin S := fmk S (nhi S - 1)

/-- The class-1 partner of a class-0 state. -/
def upF [NeZero S] (s : Fin S) : Fin S :=
  if s.val < nlo S then fmk S (s.val + nhi S) else fmk S (nhi S)

/-- The class-0 partner of a class-1 state. -/
def downF [NeZero S] (t : Fin S) : Fin S := fmk S (t.val - nhi S)

/-- The reward/class function: `0` on class 0, `1` on class 1. -/
def rhoF (s : Fin S) : ℝ := if s.val < nhi S then 0 else 1

/-- Navigation.  At a graph state the arm actions are self-loops, the first
`digs A` navigation actions run the de Bruijn step and the last one escapes to
`xtra`; the leftover class-0 state always moves to state `0`. -/
def navF [NeZero S] [NeZero (nlo S)] (s : Fin S) (b : Fin A) : Fin S :=
  if s.val < nlo S then
    (if b.val < arms A then s
     else if b.val - arms A < digs A then
       ofZ (toZ s * (digs A : ZMod (nlo S)) + ((b.val - arms A : ℕ) : ZMod (nlo S)))
     else xtra S)
  else fmk S 0

/-- The planted (state, action) pairs. -/
def armF [NeZero S] [NeZero A] (i : Fin (S / 2 * (A / 2))) : Fin S × Fin A :=
  (fmk S (i.val / arms A), fmk A (i.val % arms A))

section Facts

lemma nlo_pos (hS : 10 ≤ S) : 0 < nlo S := by simp only [nlo]; omega

lemma nhi_lt (hS : 10 ≤ S) : nhi S < S := by simp only [nhi]; omega

lemma nlo_le_nhi (hS : 10 ≤ S) : nlo S ≤ nhi S := by simp only [nlo, nhi]; omega

lemma xtra_lt [NeZero S] (hS : 10 ≤ S) : (xtra S).val < nhi S := by
  rw [xtra, fmk_val (by simp only [nhi]; omega)]
  simp only [nhi]; omega

lemma upF_val_lo [NeZero S] (hS : 10 ≤ S) {s : Fin S} (h : s.val < nlo S) :
    (upF s).val = s.val + nhi S := by
  rw [upF, if_pos h]
  exact fmk_val (by simp only [nlo] at h; simp only [nhi]; omega)

lemma upF_ge [NeZero S] (hS : 10 ≤ S) (s : Fin S) : nhi S ≤ (upF s).val := by
  rw [upF]
  split_ifs with h
  · rw [fmk_val (by simp only [nlo] at h; simp only [nhi]; omega)]; omega
  · rw [fmk_val (nhi_lt hS)]

lemma downF_val [NeZero S] {t : Fin S} (h : nhi S ≤ t.val) :
    (downF t).val = t.val - nhi S := by
  rw [downF]
  refine fmk_val ?_
  have := t.isLt
  omega

lemma downF_lt [NeZero S] (hS : 10 ≤ S) {t : Fin S} (h : nhi S ≤ t.val) :
    (downF t).val < nlo S := by
  rw [downF_val h]
  have h2 := t.isLt
  simp only [nlo, nhi] at *
  omega

lemma downF_upF [NeZero S] (hS : 10 ≤ S) {s : Fin S} (h : s.val < nlo S) :
    downF (upF s) = s := by
  apply Fin.ext
  rw [downF_val (by rw [upF_val_lo hS h]; omega), upF_val_lo hS h]
  omega

lemma upF_downF [NeZero S] (hS : 10 ≤ S) {t : Fin S} (h : nhi S ≤ t.val) :
    upF (downF t) = t := by
  apply Fin.ext
  rw [upF_val_lo hS (downF_lt hS h), downF_val h]
  have := t.isLt
  omega

lemma navF_lt [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (s : Fin S) (b : Fin A) :
    (navF s b).val < nhi S := by
  rw [navF]
  split_ifs with h1 h2 h3
  · have := nlo_le_nhi hS; omega
  · have := ofZ_lt (S := S) (toZ s * (digs A : ZMod (nlo S)) + ((b.val - arms A : ℕ) : ZMod (nlo S)))
    have := nlo_le_nhi hS
    omega
  · exact xtra_lt hS
  · rw [fmk_val (by omega)]; simp only [nhi]; omega

lemma upF_ne_navF [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (s : Fin S) (b : Fin A) :
    upF s ≠ navF s b := by
  intro hc
  have h1 := upF_ge hS s
  have h2 := navF_lt hS s b
  rw [hc] at h1
  omega

lemma downF_ne [NeZero S] (hS : 10 ≤ S) {t : Fin S} (h : nhi S ≤ t.val) :
    downF t ≠ t := by
  intro hc
  have h3 := downF_lt hS h
  have := nlo_le_nhi hS
  rw [hc] at h3
  omega

lemma rhoF_zero {s : Fin S} (h : s.val < nhi S) : rhoF s = 0 := by rw [rhoF, if_pos h]

lemma rhoF_one {s : Fin S} (h : ¬ s.val < nhi S) : rhoF s = 1 := by rw [rhoF, if_neg h]

lemma rhoF_eq_zero_iff {s : Fin S} : rhoF s = 0 ↔ s.val < nhi S := by
  rw [rhoF]; split_ifs with h <;> simp [h]

end Facts

/-! ### Two-point rows -/

/-- A probability row supported on (at most) the two states `x` and `y`. -/
noncomputable def tworow (x y : Fin S) (u v : ℝ) : Fin S → ℝ≥0 :=
  fun s' => (if s' = x then u.toNNReal else 0) + (if s' = y then v.toNNReal else 0)

lemma tworow_sum (x y : Fin S) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    ∑ s', tworow x y u v s' = 1 := by
  simp only [tworow]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x (fun _ => u.toNNReal),
    Finset.sum_ite_eq' Finset.univ y (fun _ => v.toNNReal)]
  simp only [Finset.mem_univ, if_true]
  rw [← NNReal.coe_inj]
  push_cast
  rw [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv]
  exact huv

lemma tworow_fst {x y : Fin S} (h : x ≠ y) {u v : ℝ} (hu : 0 ≤ u) :
    ((tworow x y u v x : ℝ≥0) : ℝ) = u := by
  simp only [tworow, if_neg h]
  push_cast
  rw [Real.coe_toNNReal _ hu]
  ring

lemma tworow_snd {x y : Fin S} (h : x ≠ y) {u v : ℝ} (hv : 0 ≤ v) :
    ((tworow x y u v y : ℝ≥0) : ℝ) = v := by
  simp only [tworow, if_neg (Ne.symm h)]
  push_cast
  rw [Real.coe_toNNReal _ hv]
  ring

lemma tworow_expect (x y : Fin S) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (V : Fin S → ℝ) :
    ∑ s', ((tworow x y u v s' : ℝ≥0) : ℝ) * V s' = u * V x + v * V y := by
  have key : ∀ s' : Fin S, ((tworow x y u v s' : ℝ≥0) : ℝ) * V s'
      = (if s' = x then u * V s' else 0) + (if s' = y then v * V s' else 0) := by
    intro s'
    simp only [tworow, NNReal.coe_add]
    split_ifs <;>
      simp only [NNReal.coe_zero, Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv] <;> ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x (fun s' => u * V s'),
    Finset.sum_ite_eq' Finset.univ y (fun s' => v * V s')]
  simp

/-! ### The MDP -/

/-- The transition row of the gadget: from class 0 the perturbed two-point row
`(up s, nav s b)`, from class 1 the row `(down s, s)`. -/
noncomputable def rowF [NeZero S] [NeZero (nlo S)] (D : ℝ) (e : Fin S → Fin A → ℝ)
    (s : Fin S) (b : Fin A) : Fin S → ℝ≥0 :=
  if s.val < nhi S then tworow (upF s) (navF s b) (4 / D + e s b) (1 - 4 / D - e s b)
  else tworow (downF s) s (4 / D) (1 - 4 / D)

/-- The gadget MDP with perturbation `e`. -/
noncomputable def mdpF [NeZero S] [NeZero (nlo S)] (D : ℝ) (e : Fin S → Fin A → ℝ)
    (hlo : ∀ s b, 0 ≤ 4 / D + e s b) (hhi : ∀ s b, 4 / D + e s b ≤ 1)
    (hd0 : 0 ≤ 4 / D) (hd1 : 4 / D ≤ 1) : FiniteMDP S A where
  P := rowF D e
  P_sum_one := by
    intro s b
    rw [rowF]
    split_ifs with h
    · exact tworow_sum _ _ (hlo s b) (by linarith [hhi s b]) (by ring)
    · exact tworow_sum _ _ hd0 (by linarith) (by ring)
  r := fun s _ => rhoF s
  r_mem_Icc := by
    intro s a
    rw [Set.mem_Icc, rhoF]
    split_ifs <;> norm_num

/-! ### The de Bruijn depth fits inside the diameter budget -/

lemma pow_bound (S A : ℕ) (hS : 10 ≤ S) (hA : 10 ≤ A) (D : ℝ) (hD : 12 ≤ D)
    (hlog : 20 * (Real.log S / Real.log A) ≤ D) (L : ℕ) (hLD : D / 4 - 2 ≤ (L : ℝ)) :
    nlo S ≤ digs A ^ L := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA8 : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 8 ≤ A)
  have hx8 : (3 : ℝ) * Real.log 2 ≤ Real.log A := by
    have h1 : Real.log 8 ≤ Real.log A := Real.log_le_log (by norm_num) hA8
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have hxpos : 0 < Real.log A := by linarith
  have hy : Real.log S ≤ D / 20 * Real.log A := by
    have h1 : Real.log S / Real.log A ≤ D / 20 := by linarith
    exact (div_le_iff₀ hxpos).mp h1
  have hApos : (0 : ℝ) < (A : ℝ) := by linarith
  -- the digit alphabet is at least `2A/5`
  have hkA : (2 : ℝ) * A / 5 ≤ (digs A : ℝ) := by
    have h : 2 * A ≤ 5 * digs A := by simp only [digs]; omega
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  have hkpos : (0 : ℝ) < (digs A : ℝ) := by linarith
  -- `log (5/2) ≤ (3/2) log 2`
  have hu : Real.log (5 / 2) ≤ 3 / 2 * Real.log 2 := by
    have h1 : Real.log ((5 / 2 : ℝ) ^ (2 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogk : Real.log A - Real.log (5 / 2) ≤ Real.log (digs A) := by
    have h1 : Real.log ((A : ℝ) / (5 / 2)) ≤ Real.log (digs A) :=
      Real.log_le_log (by positivity) (by linarith)
    rwa [Real.log_div (ne_of_gt hApos) (by norm_num)] at h1
  have key : D / 20 * Real.log A - Real.log 2
      ≤ (D / 4 - 2) * (Real.log A - Real.log (5 / 2)) := by
    have h3 : (0 : ℝ) ≤ D - 12 := by linarith
    have h4 : (0 : ℝ) ≤ Real.log A / 5 - 3 / 8 * Real.log 2 := by linarith
    have h5 : (0 : ℝ) ≤ (D / 4 - 2) * (3 / 2 * Real.log 2 - Real.log (5 / 2)) := by
      apply mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg h3 h4]
  have hmain : Real.log S - Real.log 2 ≤ (L : ℝ) * Real.log (digs A) :=
    calc Real.log S - Real.log 2 ≤ D / 20 * Real.log A - Real.log 2 := by linarith
      _ ≤ (D / 4 - 2) * (Real.log A - Real.log (5 / 2)) := key
      _ ≤ (L : ℝ) * (Real.log A - Real.log (5 / 2)) :=
          mul_le_mul_of_nonneg_right hLD (by linarith)
      _ ≤ (L : ℝ) * Real.log (digs A) :=
          mul_le_mul_of_nonneg_left hlogk (Nat.cast_nonneg _)
  have hnpos : (0 : ℝ) < (nlo S : ℝ) := by
    have : 0 < nlo S := nlo_pos hS
    exact_mod_cast this
  have hnS : (nlo S : ℝ) ≤ (S : ℝ) / 2 := by
    have h : 2 * nlo S ≤ S := by simp only [nlo]; omega
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    have : (10 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    linarith
  have hlogn : Real.log (nlo S) ≤ Real.log S - Real.log 2 := by
    have h1 : Real.log (nlo S) ≤ Real.log ((S : ℝ) / 2) := Real.log_le_log hnpos hnS
    rwa [Real.log_div (ne_of_gt hSpos) (by norm_num)] at h1
  have hfin : (nlo S : ℝ) ≤ (digs A : ℝ) ^ L := by
    by_contra hcon
    push_neg at hcon
    have h1 := Real.log_lt_log (by positivity) hcon
    rw [Real.log_pow] at h1
    linarith
  exact_mod_cast hfin

/-- Reduce the diameter bound to exhibiting one policy per ordered pair. -/
lemma diameter_le_of_forall {S A : ℕ} (M : FiniteMDP S A) (D : ℝ)
    (h : ∀ src tgt : Fin S, src ≠ tgt →
      ∃ f : Fin S → Fin A, mdpTravelTime M f src tgt ≤ ENNReal.ofReal D) :
    mdpDiameterENN M ≤ ENNReal.ofReal D := by
  rw [mdpDiameterENN]
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun hne => ?_
  obtain ⟨f, hf⟩ := h src tgt hne
  exact le_trans (iInf_le _ f) hf

/-! ### The diameter bound -/

lemma drift_sum0 [NeZero S] [NeZero (nlo S)] (D : ℝ) (e : Fin S → Fin A → ℝ)
    (hlo : ∀ s b, 0 ≤ 4 / D + e s b) (hhi : ∀ s b, 4 / D + e s b ≤ 1)
    (hd0 : 0 ≤ 4 / D) (hd1 : 4 / D ≤ 1)
    {s : Fin S} (hs : s.val < nhi S) (b : Fin A) (V : Fin S → ℝ) :
    ∑ s', (((mdpF D e hlo hhi hd0 hd1).P s b s' : ℝ≥0) : ℝ) * V s'
      = (4 / D + e s b) * V (upF s) + (1 - 4 / D - e s b) * V (navF s b) := by
  show ∑ s', ((rowF D e s b s' : ℝ≥0) : ℝ) * V s' = _
  rw [rowF, if_pos hs]
  exact tworow_expect _ _ (hlo s b) (by linarith [hhi s b]) V

lemma drift_sum1 [NeZero S] [NeZero (nlo S)] (D : ℝ) (e : Fin S → Fin A → ℝ)
    (hlo : ∀ s b, 0 ≤ 4 / D + e s b) (hhi : ∀ s b, 4 / D + e s b ≤ 1)
    (hd0 : 0 ≤ 4 / D) (hd1 : 4 / D ≤ 1)
    {s : Fin S} (hs : ¬ s.val < nhi S) (b : Fin A) (V : Fin S → ℝ) :
    ∑ s', (((mdpF D e hlo hhi hd0 hd1).P s b s' : ℝ≥0) : ℝ) * V s'
      = (4 / D) * V (downF s) + (1 - 4 / D) * V s := by
  show ∑ s', ((rowF D e s b s' : ℝ≥0) : ℝ) * V s' = _
  rw [rowF, if_neg hs]
  exact tworow_expect _ _ hd0 (by linarith) V

set_option maxHeartbeats 2000000 in
lemma diameter_bound {S A : ℕ} [NeZero S] [NeZero A] [NeZero (nlo S)]
    (hS : 10 ≤ S) (hA : 10 ≤ A) (D : ℝ) (hD : 12 ≤ D)
    (hlog : 20 * (Real.log S / Real.log A) ≤ D)
    (e : Fin S → Fin A → ℝ) (he0 : ∀ s b, 0 ≤ e s b)
    (henav : ∀ s b, arms A ≤ b.val → e s b = 0)
    (hlo : ∀ s b, 0 ≤ 4 / D + e s b) (hhi : ∀ s b, 4 / D + e s b ≤ 1)
    (hd0 : 0 ≤ 4 / D) (hd1 : 4 / D ≤ 1) :
    mdpDiameterENN (mdpF D e hlo hhi hd0 hd1) ≤ ENNReal.ofReal D := by
  classical
  have hnn : nhi S ≤ nlo S + 1 := by simp only [nlo, nhi]; omega
  have hnlonhi : nlo S ≤ nhi S := nlo_le_nhi hS
  have hdigs : 0 < digs A := by simp only [digs]; omega
  have harmsA : arms A < A := by simp only [arms]; omega
  have hsum : arms A + digs A < A := by simp only [arms, digs]; omega
  -- numeric preamble
  have hDpos : (0 : ℝ) < D := by linarith
  have hD4 : (0 : ℝ) < D - 4 := by linarith
  set δ : ℝ := 4 / D with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ3 : δ ≤ 1 / 3 := by
    rw [hδdef, div_le_div_iff₀ hDpos (by norm_num)]; linarith
  set γ : ℝ := 2 * D / (D - 4) with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  have hγ2 : (1 - δ) * γ = 2 := by rw [hδdef, hγdef]; field_simp
  have hγ2' : (2 : ℝ) ≤ γ := by nlinarith
  have hγD : γ ≤ D / 4 := by
    rw [hγdef, div_le_div_iff₀ hD4 (by norm_num)]; nlinarith
  have hinvδ : 1 / δ = D / 4 := by rw [hδdef]; field_simp
  -- the de Bruijn depth
  obtain ⟨L, hLD, hLD2⟩ : ∃ L : ℕ, D / 4 - 2 ≤ (L : ℝ) ∧ (L : ℝ) ≤ D / 4 - 1 := by
    have hfl : 3 ≤ ⌊D / 4⌋₊ := Nat.le_floor (by push_cast; linarith)
    have h1 := Nat.lt_floor_add_one (D / 4)
    have h2 := Nat.floor_le (show (0 : ℝ) ≤ D / 4 by linarith)
    refine ⟨⌊D / 4⌋₊ - 1, ?_, ?_⟩ <;>
      · rw [Nat.cast_sub (by omega : 1 ≤ ⌊D / 4⌋₊)]
        push_cast
        linarith
  have hLpow : nlo S ≤ digs A ^ L := pow_bound S A hS hA D hD hlog L hLD
  have hbud1 : γ * (L : ℝ) ≤ D / 2 := by
    rw [hγdef, div_mul_eq_mul_div, div_le_div_iff₀ hD4 (by norm_num)]
    nlinarith
  clear hlog hLD
  apply diameter_le_of_forall
  intro src tgt hne
  by_cases hxt : nlo S ≤ tgt.val ∧ tgt.val < nhi S
  · -- the target is the leftover class-0 state; one escape step suffices
    have htgtx : tgt = xtra S := by
      apply Fin.ext
      rw [xtra, fmk_val (by simp only [nhi]; omega)]
      omega
    set V : Fin S → ℝ :=
      fun s => if s = tgt then 0 else (if s.val < nhi S then γ else γ + 1 / δ) with hVdef
    have hVnn : ∀ s, 0 ≤ V s := by
      intro s; simp only [hVdef]
      split_ifs
      · exact le_refl 0
      · linarith
      · have : 0 < 1 / δ := by positivity
        linarith
    refine ⟨fun _ => fmk A (arms A + digs A), ?_⟩
    refine le_trans (BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift _ _ src tgt V hVnn ?_)
      (ENNReal.ofReal_le_ofReal ?_)
    · intro s hstgt
      by_cases hs0 : s.val < nhi S
      · have hslo : s.val < nlo S := by
          by_contra hcon
          exact hstgt (Fin.ext (by omega))
        rw [drift_sum0 D e hlo hhi hd0 hd1 hs0]
        have hbval : (fmk A (arms A + digs A)).val = arms A + digs A := fmk_val hsum
        have hnav : navF s (fmk A (arms A + digs A)) = tgt := by
          rw [navF, if_pos hslo, hbval, if_neg (by omega), if_neg (by omega), htgtx]
        have he : e s (fmk A (arms A + digs A)) = 0 := henav _ _ (by rw [hbval]; omega)
        have hup1 : ¬ (upF s).val < nhi S := by have := upF_ge hS s; omega
        have hupne : upF s ≠ tgt := by
          intro hc; rw [hc] at hup1; exact hup1 (by omega)
        have hVup : V (upF s) = γ + 1 / δ := by
          rw [hVdef]; dsimp only; rw [if_neg hupne, if_neg hup1]
        have hVs : V s = γ := by rw [hVdef]; dsimp only; rw [if_neg hstgt, if_pos hs0]
        have hVt : V tgt = 0 := by simp only [hVdef, if_pos rfl]
        rw [hnav, he, hVup, hVt, hVs]
        have : δ * (1 / δ) = 1 := by field_simp
        nlinarith
      · rw [drift_sum1 D e hlo hhi hd0 hd1 hs0]
        have hdlo : (downF s).val < nlo S := downF_lt hS (by omega)
        have hdne : downF s ≠ tgt := by
          intro hc; rw [hc] at hdlo; omega
        have hVd : V (downF s) = γ := by
          rw [hVdef]; dsimp only; rw [if_neg hdne, if_pos (by omega : (downF s).val < nhi S)]
        have hVs : V s = γ + 1 / δ := by
          rw [hVdef]; dsimp only; rw [if_neg hstgt, if_neg hs0]
        rw [hVd, hVs]
        have hone : δ * (1 / δ) = 1 := by field_simp
        nlinarith
    · have hVle : V src ≤ γ + 1 / δ := by
        simp only [hVdef]
        split_ifs
        · positivity
        · have : 0 < 1 / δ := by positivity
          linarith
        · exact le_refl _
      rw [hinvδ] at hVle
      linarith
  · -- the target is a graph state or a class-1 state
    rw [not_and_or, not_le, not_lt] at hxt
    set z : ZMod (nlo S) := if tgt.val < nlo S then toZ tgt else toZ (downF tgt) with hzdef
    set b0 : ℝ := if tgt.val < nhi S then 0 else 1 with hbdef
    have hbnn : 0 ≤ b0 := by rw [hbdef]; split_ifs <;> norm_num
    have hble : b0 ≤ 1 := by rw [hbdef]; split_ifs <;> norm_num
    have hz : ∀ s : Fin S, s.val < nlo S → toZ s = z → s = tgt ∨ upF s = tgt := by
      intro s hslo hsz
      rcases hxt with h | h
      · left
        rw [hzdef, if_pos h] at hsz
        have := congrArg (ofZ (S := S)) hsz
        rwa [ofZ_toZ hslo, ofZ_toZ h] at this
      · right
        rw [hzdef, if_neg (by omega)] at hsz
        have hdl : (downF tgt).val < nlo S := downF_lt hS h
        have := congrArg (ofZ (S := S)) hsz
        rw [ofZ_toZ hslo, ofZ_toZ hdl] at this
        rw [this, upF_downF hS h]
    obtain ⟨jj, hjjlt, hjjdec⟩ :
        ∃ jj : Fin S → ℕ, (∀ s, jj s < digs A) ∧
          (∀ s : Fin S, toZ s ≠ z →
            dst (k := digs A) z
                (toZ s * (digs A : ZMod (nlo S)) + ((jj s : ℕ) : ZMod (nlo S)))
              < dst (k := digs A) z (toZ s)) := by
      have H : ∀ s : Fin S, ∃ j : ℕ, j < digs A ∧ (toZ s ≠ z →
          dst (k := digs A) z (toZ s * (digs A : ZMod (nlo S)) + ((j : ℕ) : ZMod (nlo S)))
            < dst (k := digs A) z (toZ s)) := by
        intro s
        by_cases h : toZ s ≠ z
        · obtain ⟨j, hj1, hj2⟩ := exists_digit hLpow hdigs z (toZ s) h
          exact ⟨j, hj1, fun _ => hj2⟩
        · exact ⟨0, hdigs, fun hc => absurd hc h⟩
      choose jj h1 h2 using H
      exact ⟨jj, h1, h2⟩
    set d0 : ℕ := dst (k := digs A) z 0 with hd0def
    obtain ⟨W, hWlo, hWhi⟩ : ∃ W : Fin S → ℝ,
        (∀ s : Fin S, s.val < nlo S → W s = γ * ((dst (k := digs A) z (toZ s) : ℕ) : ℝ)) ∧
        (∀ s : Fin S, ¬ s.val < nlo S → W s = γ * (((d0 : ℕ) : ℝ) + 1)) := by
      refine ⟨fun s => if s.val < nlo S then γ * ((dst (k := digs A) z (toZ s) : ℕ) : ℝ)
        else γ * (((d0 : ℕ) : ℝ) + 1), fun s hs => ?_, fun s hs => ?_⟩
      · exact if_pos hs
      · exact if_neg hs
    have hIpos : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδpos
    have hone : δ * (1 / δ) = 1 := by rw [mul_one_div, div_self (ne_of_gt hδpos)]
    have hWnn : ∀ s, 0 ≤ W s := by
      intro s
      by_cases h : s.val < nlo S
      · rw [hWlo s h]
        exact mul_nonneg (le_of_lt hγpos) (Nat.cast_nonneg _)
      · rw [hWhi s h]
        refine mul_nonneg (le_of_lt hγpos) ?_
        have h2 : (0 : ℝ) ≤ ((d0 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    obtain ⟨V, hVt, hV0eq, hV1eq⟩ : ∃ V : Fin S → ℝ,
        V tgt = 0 ∧
        (∀ s : Fin S, s.val < nhi S → s ≠ tgt → V s = W s + (1 / δ) * b0) ∧
        (∀ s : Fin S, ¬ s.val < nhi S → s ≠ tgt →
          V s = W (downF s) + (1 / δ) * (b0 + 1)) := by
      refine ⟨fun s => if s = tgt then 0 else
        (if s.val < nhi S then W s + (1 / δ) * b0 else W (downF s) + (1 / δ) * (b0 + 1)),
        if_pos rfl, fun s hs hst => ?_, fun s hs hst => ?_⟩
      · simp only [if_neg hst, if_pos hs]
      · simp only [if_neg hst, if_neg hs]
    have hVnn : ∀ s, 0 ≤ V s := by
      intro s
      by_cases hst : s = tgt
      · rw [hst, hVt]
      · by_cases hs : s.val < nhi S
        · rw [hV0eq s hs hst]
          exact add_nonneg (hWnn s) (mul_nonneg (le_of_lt hIpos) hbnn)
        · rw [hV1eq s hs hst]
          exact add_nonneg (hWnn (downF s))
            (mul_nonneg (le_of_lt hIpos) (by linarith))
    have hV0le : ∀ s : Fin S, s.val < nhi S → V s ≤ W s + (1 / δ) * b0 := by
      intro s hs
      by_cases hst : s = tgt
      · rw [hst, hVt, ← hst]
        exact add_nonneg (hWnn s) (mul_nonneg (le_of_lt hIpos) hbnn)
      · rw [hV0eq s hs hst]
    have hV1le : ∀ s : Fin S, ¬ s.val < nhi S → V s ≤ W (downF s) + (1 / δ) * (b0 + 1) := by
      intro s hs
      by_cases hst : s = tgt
      · rw [hst, hVt, ← hst]
        exact add_nonneg (hWnn (downF s)) (mul_nonneg (le_of_lt hIpos) (by linarith))
      · rw [hV1eq s hs hst]
    have hdle : ∀ x : ZMod (nlo S), ((dst (k := digs A) z x : ℕ) : ℝ) ≤ (L : ℝ) := by
      intro x; exact_mod_cast dst_le hLpow z x
    have hWL : ∀ s : Fin S, s.val < nlo S → W s ≤ γ * (L : ℝ) := by
      intro s hs; rw [hWlo s hs]
      exact mul_le_mul_of_nonneg_left (hdle _) (le_of_lt hγpos)
    -- the state `0` and its potential
    have hs0lt : (fmk S 0).val < nlo S := by
      rw [fmk_val (by omega)]; exact nlo_pos hS
    have htoZ0 : toZ (fmk S 0) = (0 : ZMod (nlo S)) := by
      rw [toZ, fmk_val (by omega)]; simp
    have hW0 : W (fmk S 0) = γ * ((d0 : ℕ) : ℝ) := by
      rw [hWlo _ hs0lt, htoZ0]
    refine ⟨fun s => if s.val < nlo S then
        (if toZ s = z then fmk A 0 else fmk A (arms A + jj s)) else fmk A (arms A), ?_⟩
    refine le_trans (BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift _ _ src tgt V hVnn ?_)
      (ENNReal.ofReal_le_ofReal ?_)
    · intro s hstgt
      by_cases hs0 : s.val < nhi S
      · by_cases hslo : s.val < nlo S
        · by_cases hsz : toZ s = z
          · -- at the target's residue: use an arm self-loop, the up-move hits the target
            have hup : upF s = tgt := by
              rcases hz s hslo hsz with h | h
              · exact absurd h hstgt
              · exact h
            have hbv : (fmk A 0).val = 0 := fmk_val (by omega)
            have harm : (0 : ℕ) < arms A := by simp only [arms]; omega
            have hnav : navF s (fmk A 0) = s := by
              rw [navF, if_pos hslo, hbv, if_pos harm]
            have hfs : (if s.val < nlo S then
                (if toZ s = z then fmk A 0 else fmk A (arms A + jj s))
                else fmk A (arms A)) = fmk A 0 := by rw [if_pos hslo, if_pos hsz]
            rw [hfs, drift_sum0 D e hlo hhi hd0 hd1 hs0, hnav, hup]
            have hbone : b0 = 1 := by
              rw [hbdef, if_neg (by have := upF_ge hS s; rw [hup] at this; omega)]
            have hd : dst (k := digs A) z (toZ s) = 0 :=
              (dst_eq_zero_iff hLpow z (toZ s)).mpr hsz
            have hVs : V s = 1 / δ := by
              rw [hV0eq s hs0 hstgt, hWlo s hslo, hd, hbone]
              push_cast; ring
            rw [hVt, hVs]
            have hmul : 0 ≤ e s (fmk A 0) * (1 / δ) :=
              mul_nonneg (he0 _ _) (le_of_lt hIpos)
            nlinarith
          · -- navigate one de Bruijn step closer
            have hjv : (fmk A (arms A + jj s)).val = arms A + jj s :=
              fmk_val (by have := hjjlt s; omega)
            have hfs : (if s.val < nlo S then
                (if toZ s = z then fmk A 0 else fmk A (arms A + jj s))
                else fmk A (arms A)) = fmk A (arms A + jj s) := by
              rw [if_pos hslo, if_neg hsz]
            have he : e s (fmk A (arms A + jj s)) = 0 := henav _ _ (by rw [hjv]; omega)
            have hnav : navF s (fmk A (arms A + jj s))
                = ofZ (toZ s * (digs A : ZMod (nlo S)) + ((jj s : ℕ) : ZMod (nlo S))) := by
              have hsub : arms A + jj s - arms A = jj s := by omega
              rw [navF, if_pos hslo, hjv, if_neg (by omega),
                if_pos (by have := hjjlt s; omega), hsub]
            obtain ⟨s', hs'def⟩ : ∃ t : Fin S,
                ofZ (toZ s * (digs A : ZMod (nlo S)) + ((jj s : ℕ) : ZMod (nlo S))) = t :=
              ⟨_, rfl⟩
            rw [hfs, drift_sum0 D e hlo hhi hd0 hd1 hs0, he, hnav, hs'def]
            have htoZs' : toZ s'
                = toZ s * (digs A : ZMod (nlo S)) + ((jj s : ℕ) : ZMod (nlo S)) := by
              rw [← hs'def, toZ_ofZ]
            have hs'lt : s'.val < nlo S := by rw [← hs'def]; exact ofZ_lt _
            have hs'lt2 : s'.val < nhi S := by omega
            have hdec : ((dst (k := digs A) z (toZ s') : ℕ) : ℝ)
                ≤ ((dst (k := digs A) z (toZ s) : ℕ) : ℝ) - 1 := by
              have h1 : dst (k := digs A) z (toZ s')
                  < dst (k := digs A) z (toZ s) := by
                rw [htoZs']
                exact hjjdec s hsz
              have h2 : ((dst (k := digs A) z (toZ s') : ℕ) : ℝ) + 1
                  ≤ ((dst (k := digs A) z (toZ s) : ℕ) : ℝ) := by exact_mod_cast h1
              linarith
            have hVs' : V s' ≤ γ * ((dst (k := digs A) z (toZ s) : ℝ) - 1) + (1 / δ) * b0 := by
              refine le_trans (hV0le s' hs'lt2) ?_
              rw [hWlo s' hs'lt]
              have := mul_le_mul_of_nonneg_left hdec (le_of_lt hγpos)
              linarith
            have hupge : ¬ (upF s).val < nhi S := by have := upF_ge hS s; omega
            have hVup : V (upF s)
                ≤ γ * (dst (k := digs A) z (toZ s) : ℝ) + (1 / δ) * (b0 + 1) := by
              refine le_trans (hV1le _ hupge) ?_
              rw [downF_upF hS hslo, hWlo s hslo]
            have hVs : V s = γ * (dst (k := digs A) z (toZ s) : ℝ) + (1 / δ) * b0 := by
              rw [hV0eq s hs0 hstgt, hWlo s hslo]
            rw [hVs]
            have h1 : δ * V (upF s)
                ≤ δ * (γ * (dst (k := digs A) z (toZ s) : ℝ) + (1 / δ) * (b0 + 1)) :=
              mul_le_mul_of_nonneg_left hVup (le_of_lt hδpos)
            have h2 : (1 - δ) * V s'
                ≤ (1 - δ) * (γ * ((dst (k := digs A) z (toZ s) : ℝ) - 1) + (1 / δ) * b0) :=
              mul_le_mul_of_nonneg_left hVs' (by linarith)
            have h3 : δ * (γ * (dst (k := digs A) z (toZ s) : ℝ) + (1 / δ) * (b0 + 1))
                + (1 - δ) * (γ * ((dst (k := digs A) z (toZ s) : ℝ) - 1) + (1 / δ) * b0) + 1
                = γ * (dst (k := digs A) z (toZ s) : ℝ) + (1 / δ) * b0 := by
              linear_combination hone - hγ2
            linarith
        · -- the leftover class-0 state: move to state `0`
          have hbv : (fmk A (arms A)).val = arms A := fmk_val harmsA
          have hfs : (if s.val < nlo S then
              (if toZ s = z then fmk A 0 else fmk A (arms A + jj s))
              else fmk A (arms A)) = fmk A (arms A) := by rw [if_neg hslo]
          have he : e s (fmk A (arms A)) = 0 := henav _ _ (by rw [hbv])
          have hnav : navF s (fmk A (arms A)) = fmk S 0 := by rw [navF, if_neg hslo]
          rw [hfs, drift_sum0 D e hlo hhi hd0 hd1 hs0, he, hnav]
          have hupv : (upF s).val = nhi S := by
            rw [upF, if_neg hslo, fmk_val (nhi_lt hS)]
          have hupge : ¬ (upF s).val < nhi S := by omega
          have hdup : downF (upF s) = fmk S 0 := by
            apply Fin.ext
            rw [downF_val (by omega), hupv, fmk_val (by omega)]
            omega
          have hVup : V (upF s) ≤ γ * ((d0 : ℕ) : ℝ) + (1 / δ) * (b0 + 1) := by
            refine le_trans (hV1le _ hupge) ?_
            rw [hdup, hW0]
          have hV0' : V (fmk S 0) ≤ γ * ((d0 : ℕ) : ℝ) + (1 / δ) * b0 := by
            refine le_trans (hV0le _ (by omega)) ?_
            rw [hW0]
          have hVs : V s = γ * (((d0 : ℕ) : ℝ) + 1) + (1 / δ) * b0 := by
            rw [hV0eq s hs0 hstgt, hWhi s hslo]
          rw [hVs]
          have h1 : δ * V (upF s) ≤ δ * (γ * ((d0 : ℕ) : ℝ) + (1 / δ) * (b0 + 1)) :=
            mul_le_mul_of_nonneg_left hVup (le_of_lt hδpos)
          have h2 : (1 - δ) * V (fmk S 0)
              ≤ (1 - δ) * (γ * ((d0 : ℕ) : ℝ) + (1 / δ) * b0) :=
            mul_le_mul_of_nonneg_left hV0' (by linarith)
          have h3 : δ * (γ * ((d0 : ℕ) : ℝ) + (1 / δ) * (b0 + 1))
              + (1 - δ) * (γ * ((d0 : ℕ) : ℝ) + (1 / δ) * b0) + 1
              = γ * ((d0 : ℕ) : ℝ) + (1 / δ) * b0 + 2 := by
            linear_combination hone
          linarith
      · -- a class-1 state: wait for the down-move
        rw [drift_sum1 D e hlo hhi hd0 hd1 hs0]
        have hdlt : (downF s).val < nlo S := downF_lt hS (by omega)
        have hVd : V (downF s) ≤ W (downF s) + (1 / δ) * b0 := hV0le _ (by omega)
        have hVs : V s = W (downF s) + (1 / δ) * (b0 + 1) := hV1eq s hs0 hstgt
        rw [hVs]
        have h1 : δ * V (downF s) ≤ δ * (W (downF s) + (1 / δ) * b0) :=
          mul_le_mul_of_nonneg_left hVd (le_of_lt hδpos)
        have h3 : δ * (W (downF s) + (1 / δ) * b0)
            + (1 - δ) * (W (downF s) + (1 / δ) * (b0 + 1)) + 1
            = W (downF s) + (1 / δ) * (b0 + 1) := by
          linear_combination -(hone)
        linarith
    · -- the potential at the source is within budget
      have hIval : 1 / δ = D / 4 := hinvδ
      by_cases hsrc0 : src.val < nhi S
      · by_cases hsrclo : src.val < nlo S
        · have := hV0le src hsrc0
          have h2 := hWL src hsrclo
          rw [hIval] at this
          nlinarith
        · have h1 := hV0le src hsrc0
          have h2 : W src = γ * ((d0 : ℕ) : ℝ) + γ := by rw [hWhi src hsrclo]; ring
          have h3 : ((d0 : ℕ) : ℝ) ≤ (L : ℝ) := hdle _
          have h4 : γ * ((d0 : ℕ) : ℝ) ≤ γ * (L : ℝ) :=
            mul_le_mul_of_nonneg_left h3 (le_of_lt hγpos)
          rw [hIval] at h1
          nlinarith
      · have h1 := hV1le src hsrc0
        have h2 := hWL (downF src) (downF_lt hS (by omega))
        rw [hIval] at h1
        nlinarith

/-! ### Reading off the individual transition probabilities -/

lemma rowF_up [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (D : ℝ) (e : Fin S → Fin A → ℝ)
    {s : Fin S} (hs : s.val < nhi S) (b : Fin A) (hu : 0 ≤ 4 / D + e s b) :
    ((rowF D e s b (upF s) : ℝ≥0) : ℝ) = 4 / D + e s b := by
  rw [rowF, if_pos hs]
  exact tworow_fst (upF_ne_navF hS s b) hu

lemma rowF_nav [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (D : ℝ) (e : Fin S → Fin A → ℝ)
    {s : Fin S} (hs : s.val < nhi S) (b : Fin A) (hv : 0 ≤ 1 - 4 / D - e s b) :
    ((rowF D e s b (navF s b) : ℝ≥0) : ℝ) = 1 - 4 / D - e s b := by
  rw [rowF, if_pos hs]
  exact tworow_snd (upF_ne_navF hS s b) hv

lemma rowF_down [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (D : ℝ) (e : Fin S → Fin A → ℝ)
    {s : Fin S} (hs : ¬ s.val < nhi S) (b : Fin A) (hu : 0 ≤ 4 / D) :
    ((rowF D e s b (downF s) : ℝ≥0) : ℝ) = 4 / D := by
  rw [rowF, if_neg hs]
  exact tworow_fst (downF_ne hS (by omega)) hu

lemma rowF_self [NeZero S] [NeZero (nlo S)] (hS : 10 ≤ S) (D : ℝ) (e : Fin S → Fin A → ℝ)
    {s : Fin S} (hs : ¬ s.val < nhi S) (b : Fin A) (hv : 0 ≤ 1 - 4 / D) :
    ((rowF D e s b s : ℝ≥0) : ℝ) = 1 - 4 / D := by
  rw [rowF, if_neg hs]
  exact tworow_snd (downF_ne hS (by omega)) hv

lemma armF_fst_lt [NeZero S] [NeZero A] (hS : 10 ≤ S) (hA : 10 ≤ A)
    (i : Fin (S / 2 * (A / 2))) : (armF i).1.val < nlo S := by
  have harmpos : 0 < arms A := by simp only [arms]; omega
  have hnloS : nlo S ≤ S := by simp only [nlo]; omega
  have hdlt : i.val / arms A < nlo S :=
    (Nat.div_lt_iff_lt_mul harmpos).mpr (by simpa [Nat.mul_comm] using i.isLt)
  show (fmk S (i.val / arms A)).val < nlo S
  rw [fmk_val (by omega)]
  exact hdlt

lemma armF_snd_lt [NeZero S] [NeZero A] (hA : 10 ≤ A) (i : Fin (S / 2 * (A / 2))) :
    (armF (S := S) i).2.val < arms A := by
  have harmpos : 0 < arms A := by simp only [arms]; omega
  have harmsA : arms A < A := by simp only [arms]; omega
  have hmod : i.val % arms A < arms A := Nat.mod_lt _ harmpos
  show (fmk A (i.val % arms A)).val < arms A
  rw [fmk_val (by omega)]
  exact hmod

lemma armF_inj [NeZero S] [NeZero A] (hS : 10 ≤ S) (hA : 10 ≤ A) :
    Function.Injective (armF (S := S) (A := A)) := by
  have harmpos : 0 < arms A := by simp only [arms]; omega
  have hnloS : nlo S ≤ S := by simp only [nlo]; omega
  have harmsA : arms A < A := by simp only [arms]; omega
  have hdlt : ∀ i : Fin (S / 2 * (A / 2)), i.val / arms A < nlo S := by
    intro i
    exact (Nat.div_lt_iff_lt_mul harmpos).mpr (by simpa [Nat.mul_comm] using i.isLt)
  intro i j hij
  have h1 : (fmk S (i.val / arms A)).val = (fmk S (j.val / arms A)).val :=
    congrArg Fin.val (congrArg Prod.fst hij)
  have h2 : (fmk A (i.val % arms A)).val = (fmk A (j.val % arms A)).val :=
    congrArg Fin.val (congrArg Prod.snd hij)
  have hi := hdlt i
  have hj := hdlt j
  have mi : i.val % arms A < arms A := Nat.mod_lt _ harmpos
  have mj : j.val % arms A < arms A := Nat.mod_lt _ harmpos
  rw [fmk_val (by omega : i.val / arms A < S), fmk_val (by omega : j.val / arms A < S)] at h1
  rw [fmk_val (by omega : i.val % arms A < A), fmk_val (by omega : j.val % arms A < A)] at h2
  apply Fin.ext
  calc i.val = arms A * (i.val / arms A) + i.val % arms A := (Nat.div_add_mod _ _).symm
    _ = arms A * (j.val / arms A) + j.val % arms A := by rw [h1, h2]
    _ = j.val := Nat.div_add_mod _ _

end Gadget

end JaoConstr

open JaoConstr

theorem solution :
    ∀ S A : ℕ, 10 ≤ S → 10 ≤ A → ∀ D : ℝ, 12 ≤ D →
      20 * (Real.log S / Real.log A) ≤ D →
        ∀ ε : ℝ, 0 ≤ ε → 20 * ε ≤ 4 / D →
          ∃ (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
            (arm : Fin (S / 2 * (A / 2)) → Fin S × Fin A)
            (M : Fin (S / 2 * (A / 2)) → FiniteMDP S A) (M₀ : FiniteMDP S A),
            Function.Injective arm ∧
            (∀ i, ρ (arm i).1 = 0) ∧
            (∀ i, nav (arm i).1 (arm i).2 = (arm i).1) ∧
            (∀ i, down (up (arm i).1) = (arm i).1) ∧
            (∀ s, ρ s = 0 ∨ ρ s = 1) ∧
            (∀ s b, M₀.r s b = ρ s) ∧
            (∀ s b, ρ s = 0 →
                ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
                (M₀.P s b (up s) : ℝ) = 4 / D ∧
                (M₀.P s b (nav s b) : ℝ) = 1 - 4 / D) ∧
            (∀ s b, ρ s = 1 →
                ρ (down s) = 0 ∧ down s ≠ s ∧
                (M₀.P s b (down s) : ℝ) = 4 / D ∧
                (M₀.P s b s : ℝ) = 1 - 4 / D) ∧
            (∀ i, ∀ s b, (M i).r s b = ρ s) ∧
            (∀ i, ∀ s b, ρ s = 0 →
                ((M i).P s b (up s) : ℝ)
                    = 4 / D + (if (s, b) = arm i then ε else 0) ∧
                ((M i).P s b (nav s b) : ℝ)
                    = 1 - 4 / D - (if (s, b) = arm i then ε else 0)) ∧
            (∀ i, ∀ s b, ρ s = 1 →
                ((M i).P s b (down s) : ℝ) = 4 / D ∧
                ((M i).P s b s : ℝ) = 1 - 4 / D) ∧
            (∀ i, mdpDiameterENN (M i) ≤ ENNReal.ofReal D) := by
  intro S A hS hA D hD hlog ε hε0 hε
  haveI : NeZero S := ⟨by omega⟩
  haveI : NeZero A := ⟨by omega⟩
  haveI : NeZero (nlo S) := ⟨by simp only [nlo]; omega⟩
  have hDpos : (0 : ℝ) < D := by linarith
  have hd0 : (0 : ℝ) ≤ 4 / D := by positivity
  have hd3 : (4 : ℝ) / D ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hDpos (by norm_num)]; linarith
  have hd1 : (4 : ℝ) / D ≤ 1 := by linarith
  have hεsmall : ε ≤ 1 / 60 := by linarith
  have hplo : ∀ (i : Fin (S / 2 * (A / 2))) (s : Fin S) (b : Fin A),
      0 ≤ 4 / D + (if (s, b) = armF i then ε else 0) := by
    intro i s b; split_ifs <;> linarith
  have hphi : ∀ (i : Fin (S / 2 * (A / 2))) (s : Fin S) (b : Fin A),
      4 / D + (if (s, b) = armF i then ε else 0) ≤ 1 := by
    intro i s b; split_ifs <;> linarith
  have hzlo : ∀ (_ : Fin S) (_ : Fin A), 0 ≤ 4 / D + (0 : ℝ) := fun _ _ => by linarith
  have hzhi : ∀ (_ : Fin S) (_ : Fin A), 4 / D + (0 : ℝ) ≤ 1 := fun _ _ => by linarith
  refine ⟨rhoF, upF, downF, navF, armF,
    fun i => mdpF D (fun s b => if (s, b) = armF i then ε else 0) (hplo i) (hphi i) hd0 hd1,
    mdpF D (fun _ _ => 0) hzlo hzhi hd0 hd1, armF_inj hS hA,
    fun i => rhoF_zero (by have := armF_fst_lt hS hA i; have := nlo_le_nhi hS; omega),
    fun i => ?_, fun i => downF_upF hS (armF_fst_lt hS hA i), ?_, fun s b => rfl, ?_, ?_,
    fun i s b => rfl, ?_, ?_, ?_⟩
  · rw [navF, if_pos (armF_fst_lt hS hA i), if_pos (armF_snd_lt hA i)]
  · intro s; rw [rhoF]; split_ifs <;> simp
  · intro s b hs
    have hslt : s.val < nhi S := rhoF_eq_zero_iff.mp hs
    refine ⟨rhoF_one (by have := upF_ge hS s; omega), rhoF_zero (navF_lt hS s b),
      upF_ne_navF hS s b, ?_, ?_⟩
    · show ((rowF D (fun _ _ => (0 : ℝ)) s b (upF s) : ℝ≥0) : ℝ) = 4 / D
      rw [rowF_up hS D _ hslt b (by linarith)]
      norm_num
    · show ((rowF D (fun _ _ => (0 : ℝ)) s b (navF s b) : ℝ≥0) : ℝ) = 1 - 4 / D
      rw [rowF_nav hS D _ hslt b (by linarith)]
      norm_num
  · intro s b hs
    have hslt : ¬ s.val < nhi S := by
      intro hc; rw [rhoF_zero hc] at hs; norm_num at hs
    refine ⟨rhoF_zero (by
        have := downF_lt hS (by omega : nhi S ≤ s.val)
        have := nlo_le_nhi hS
        omega), downF_ne hS (by omega), ?_, ?_⟩
    · show ((rowF D (fun _ _ => (0 : ℝ)) s b (downF s) : ℝ≥0) : ℝ) = 4 / D
      exact rowF_down hS D _ hslt b hd0
    · show ((rowF D (fun _ _ => (0 : ℝ)) s b s : ℝ≥0) : ℝ) = 1 - 4 / D
      exact rowF_self hS D _ hslt b (by linarith)
  · intro i s b hs
    have hslt : s.val < nhi S := rhoF_eq_zero_iff.mp hs
    exact ⟨rowF_up hS D _ hslt b (hplo i s b),
      rowF_nav hS D _ hslt b (by linarith [hphi i s b])⟩
  · intro i s b hs
    have hslt : ¬ s.val < nhi S := by
      intro hc; rw [rhoF_zero hc] at hs; norm_num at hs
    exact ⟨rowF_down hS D _ hslt b hd0, rowF_self hS D _ hslt b (by linarith)⟩
  · intro i
    refine diameter_bound hS hA D hD hlog _ (fun s b => by split_ifs <;> linarith) ?_ _ _ hd0 hd1
    intro s b hb
    refine if_neg ?_
    intro hc
    have hb2 : b.val = (armF (S := S) i).2.val := congrArg Fin.val (congrArg Prod.snd hc)
    have := armF_snd_lt (S := S) hA i
    omega
