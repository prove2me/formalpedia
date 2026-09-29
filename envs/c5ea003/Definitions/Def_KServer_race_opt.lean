-- Prove2me | Definitions.Def_KServer_race_opt
-- name    : KServer_race_opt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T16:36:48.637039+00:00
-- url     : https://prove2.me/theorems/316b149a-703d-422d-9f0c-ac92b7647eb1
-- title:
--   Race well-formedness: nonempty requests, pinned ending, and the follow-the-survivor offline bound
-- statement:
--   Fix the BCR race setting: four level-$w$ chunk systems $A, B_L, B_R, C$ on a metric space $X$ with entry $s$ and exit $t$, request transformations $G_A, G_L, G_R, G_{TL}, G_{TR}$ into a target space $Y$, $\kappa$ coins, and the interleaved race schedule with parks and terminal padding. This file proves the three well-formedness properties of the race as a chunk system. (1) *Nonemptiness*: every request set of every race chunk is nonempty, given that each transformation preserves nonemptiness. (2) *Pinned ending*: the flattened race sequence ends with the request $\{\mathrm{stop}\}$, given $G_{TL}\{t\} = G_{TR}\{t\} = \{\mathrm{stop}\}$ — either the padding supplies the final singleton, or (when the survivor consumed nothing in the coin phase) the mapped tail sequence ends at the image of its pinned exit. (3) *The offline bound*: for every outcome, the optimal offline evader cost of the race sequence from the start point is at most $3\,d(s,t)$. The offline strategy follows the survivor through nonexpansive lifts $\iota_A, \iota_\sigma, \iota_{T\sigma} : X \to Y$ satisfying $\iota\,'' S \subseteq G(S)$ and the junction equations $\iota_A(t) = \iota_L(s) = \iota_R(s)$, $\iota_L(t) = \iota_{TL}(s)$, $\iota_R(t) = \iota_{TR}(s)$, $\iota_{TL}(t) = \iota_{TR}(t) = \mathrm{stop}$: near-optimal offline paths of $A$, the survivor side, and the tail system are lifted and concatenated into a single reference path, the survivor's chunks advance along it, and the dead side's chunks are stationary — each of their requests contains the survivor's park, the image of the last consumed survivor request, in which the lifted path sits. The proof runs through a survivor-abstracted auxiliary theorem (the dead side enters only through the shapes of the coin chunks) instantiated for both survivor identities, and the absorb-skeleton machinery converts the chunkwise certificates into the offline bound
--   $$\mathrm{OPT}\bigl(\iota_A(s),\ \sigma_{\mathrm{race}}(\omega)\bigr) \le 3\, d(s,t) = d(\mathrm{start}, \mathrm{stop}).$$
-- source:
--   Follow-the-survivor offline strategy for the race construction in the BCR randomized k-server lower bound, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_absorb

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

/-! ### Flatten indexing and serving positions

Helpers locating a chunk-relative request inside a flattened sequence,
and the induced positions of an offline serving path: after consuming
`r` chunks the path sits in the last consumed request (the park
condition), and at the end it sits at the pinned exit. -/

section FlattenIdx

variable {α : Type*}

theorem take_flatten_succ (cs : List (List α)) {r : ℕ} (hr : r < cs.length) :
    ((cs.take (r + 1)).flatten).length
      = ((cs.take r).flatten).length + (cs[r]'hr).length := by
  rw [List.take_succ, List.flatten_append, List.length_append]
  congr 1
  rw [List.getElem?_eq_getElem hr]
  simp

theorem take_flatten_le (cs : List (List α)) (r : ℕ) :
    ((cs.take r).flatten).length ≤ cs.flatten.length := by
  conv_rhs => rw [← List.take_append_drop r cs]
  rw [List.flatten_append, List.length_append]
  omega

theorem flatten_decomp (cs : List (List α)) {r : ℕ} (hr : r < cs.length) :
    cs.flatten
      = (cs.take r).flatten ++ ((cs[r]'hr) :: cs.drop (r + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop r cs]
  rw [List.flatten_append]
  congr 2
  exact List.drop_eq_getElem_cons hr

theorem flatten_idx_lt (cs : List (List α)) {r n : ℕ} (hr : r < cs.length)
    (hn : n < (cs[r]'hr).length) :
    ((cs.take r).flatten).length + n < cs.flatten.length := by
  have hlen : cs.flatten.length = ((cs.take r).flatten).length
      + ((cs[r]'hr).length + ((cs.drop (r + 1)).flatten).length) := by
    rw [flatten_decomp cs hr, List.length_append, List.flatten_cons,
      List.length_append]
  omega

theorem flatten_getElem? (cs : List (List α)) {r n : ℕ} (hr : r < cs.length)
    (hn : n < (cs[r]'hr).length) :
    cs.flatten[((cs.take r).flatten).length + n]? = (cs[r]'hr)[n]? := by
  rw [flatten_decomp cs hr, List.getElem?_append_right (by omega),
    List.flatten_cons]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append, if_pos hn]

end FlattenIdx

section ServePos

variable (C : ChunkSystemB X s t 0 cB T pe mL)

/-- The flattened length of the first `r` chunks. -/
noncomputable def preLen (ωC : C.Ω) (r : ℕ) : ℕ :=
  (((List.ofFn (C.chunk ωC)).take r).flatten).length

theorem preLen_zero (ωC : C.Ω) : preLen C ωC 0 = 0 := rfl

theorem preLen_succ (ωC : C.Ω) {r : ℕ} (hr : r < C.m) :
    preLen C ωC (r + 1) = preLen C ωC r + (chunkN C ωC r).length := by
  unfold preLen
  rw [take_flatten_succ _ (by rw [List.length_ofFn]; exact hr),
    chunkN_lt C ωC hr]
  congr 2
  exact List.getElem_ofFn _

theorem preLen_m (ωC : C.Ω) : preLen C ωC C.m = (C.seq ωC).length := by
  unfold preLen ChunkSystemB.seq
  rw [List.take_of_length_le (by rw [List.length_ofFn])]

/-- Every request in a consumed prefix is nonempty. -/
theorem mem_take_flatten_ne (ωC : C.Ω) (idx : ℕ) {S : Set X}
    (hS : S ∈ (((List.ofFn (C.chunk ωC)).take idx).flatten)) : S.Nonempty := by
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (C.chunk ωC) := List.mem_of_mem_take hl
  rw [List.mem_ofFn] at hl2
  obtain ⟨i, rfl⟩ := hl2
  exact C.hne ωC i S hSl

/-- Every request in the full sequence is nonempty. -/
theorem mem_seq_ne (ωC : C.Ω) {S : Set X} (hS : S ∈ C.seq ωC) :
    S.Nonempty := by
  unfold ChunkSystemB.seq at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact C.hne ωC i S hSl

/-- A serving path visits a chunk-relative request at its global step. -/
theorem serves_chunk_pos (ωC : C.Ω) {P : ℕ → X}
    (hP : EvaderServes s (C.seq ωC) P) {r : ℕ} (hr : r < C.m) {n : ℕ}
    (hn : n < (chunkN C ωC r).length) :
    ((chunkN C ωC r)[n]'hn).Nonempty →
      P (preLen C ωC r + n + 1) ∈ (chunkN C ωC r)[n]'hn := by
  intro hne
  have hrl : r < (List.ofFn (C.chunk ωC)).length := by
    rw [List.length_ofFn]; exact hr
  have hchunk : (List.ofFn (C.chunk ωC))[r]'hrl = chunkN C ωC r := by
    rw [chunkN_lt C ωC hr]
    exact List.getElem_ofFn _
  have hn' : n < ((List.ofFn (C.chunk ωC))[r]'hrl).length := by
    rw [hchunk]; exact hn
  have hidx : preLen C ωC r + n < (C.seq ωC).length :=
    flatten_idx_lt (List.ofFn (C.chunk ωC)) hrl hn'
  have hq := flatten_getElem? (List.ofFn (C.chunk ωC)) hrl hn'
  rw [hchunk] at hq
  have hq2 : (C.seq ωC)[preLen C ωC r + n]? = some ((chunkN C ωC r)[n]'hn) := by
    rw [List.getElem?_eq_getElem hn] at hq
    exact hq
  have hval : (C.seq ωC)[preLen C ωC r + n]'hidx = (chunkN C ωC r)[n]'hn := by
    rw [List.getElem?_eq_getElem hidx] at hq2
    exact Option.some_injective _ hq2
  rw [evaderServes_iff] at hP
  have := hP.2 (preLen C ωC r + n) hidx (by rw [hval]; exact hne)
  rw [hval] at this
  exact this

/-- After consuming `idx` chunks the serving path is inside the last
consumed request (the park condition). -/
theorem serves_last_pos (ωC : C.Ω) {P : ℕ → X}
    (hP : EvaderServes s (C.seq ωC) P) (idx : ℕ) :
    P (preLen C ωC idx) ∈ lastXset C ωC idx := by
  unfold lastXset
  by_cases h0 : (((List.ofFn (C.chunk ωC)).take idx).flatten) = []
  · rw [h0]
    have hlen : preLen C ωC idx = 0 := by
      unfold preLen; rw [h0]; rfl
    rw [hlen, hP.1]
    simp
  · set l := ((List.ofFn (C.chunk ωC)).take idx).flatten with hl
    have hlen : 0 < l.length := List.length_pos_of_ne_nil h0
    have hgl : l.getLast? = l[l.length - 1]? := List.getLast?_eq_getElem?
    rw [hgl, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hpre : C.seq ωC = l ++ ((List.ofFn (C.chunk ωC)).drop idx).flatten := by
      show (List.ofFn (C.chunk ωC)).flatten = _
      rw [hl, ← List.flatten_append, List.take_append_drop]
    have hidx2 : l.length - 1 < (C.seq ωC).length := by
      rw [hpre, List.length_append]
      omega
    have hq : (C.seq ωC)[l.length - 1]? = l[l.length - 1]? := by
      rw [hpre, List.getElem?_append, if_pos (by omega)]
    have hval : (C.seq ωC)[l.length - 1]'hidx2 = l[l.length - 1]'(by omega) := by
      rw [List.getElem?_eq_getElem hidx2,
        List.getElem?_eq_getElem (by omega : l.length - 1 < l.length)] at hq
      exact Option.some_injective _ hq
    rw [evaderServes_iff] at hP
    have hne : (l[l.length - 1]'(by omega)).Nonempty :=
      mem_take_flatten_ne C ωC idx (List.getElem_mem _)
    have hserve := hP.2 (l.length - 1) hidx2 (by rw [hval]; exact hne)
    rw [hval] at hserve
    have hplen : preLen C ωC idx = l.length := by rw [hl]; rfl
    rw [hplen]
    rw [show l.length - 1 + 1 = l.length from by omega] at hserve
    exact hserve

/-- The sequence is nonempty. -/
theorem seq_length_pos (ωC : C.Ω) : 0 < (C.seq ωC).length := by
  by_contra h
  have h0 : C.seq ωC = [] := by
    cases hs : C.seq ωC with
    | nil => rfl
    | cons a l => rw [hs] at h; simp at h
  have := C.hlast ωC
  unfold ChunkSystemB.seq at h0
  rw [h0] at this
  simp at this

/-- The serving path ends at the pinned exit. -/
theorem serves_end (ωC : C.Ω) {P : ℕ → X}
    (hP : EvaderServes s (C.seq ωC) P) :
    P ((C.seq ωC).length) = t := by
  have hlen := seq_length_pos C ωC
  have hgl : (C.seq ωC).getLast? = some {t} := C.hlast ωC
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hgl
  have hval : (C.seq ωC)[(C.seq ωC).length - 1]'(by omega) = {t} :=
    Option.some_injective _ hgl
  rw [evaderServes_iff] at hP
  have hserve := hP.2 ((C.seq ωC).length - 1) (by omega)
    (by rw [hval]; exact Set.singleton_nonempty t)
  rw [hval] at hserve
  rw [show (C.seq ωC).length - 1 + 1 = (C.seq ωC).length from by omega] at hserve
  exact Set.mem_singleton_iff.mp hserve

end ServePos

section Spine

variable {M : Type*} [MetricSpace M]

/-- Build an absorb derivation over an indexed chunk family from per-index
advance/stationary certificates against a position schedule `p`. -/
theorem absorb_build (Q : ℕ → M) (F : ℕ → List (Set M)) (p : ℕ → ℕ) :
    ∀ (m start : ℕ),
    (∀ r, start ≤ r → r < start + m →
      (p (r + 1) = p r + (F r).length ∧
        ∀ n : ℕ, ∀ hn : n < (F r).length,
          ((F r)[n]'hn).Nonempty → Q (p r + n + 1) ∈ (F r)[n]'hn)
      ∨ (p (r + 1) = p r ∧ ∀ S ∈ F r, S.Nonempty → Q (p r) ∈ S)) →
    Absorb Q (p start) (List.ofFn (fun i : Fin m => F (start + (i : ℕ))))
      (p (start + m)) := by
  intro m
  induction m with
  | zero =>
    intro start h
    rw [Nat.add_zero]
    exact Absorb.nil _
  | succ m ih =>
    intro start h
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Nat.add_zero]
    have htail : (fun i : Fin m => F (start + ((i.succ : Fin (m + 1)) : ℕ)))
        = fun i : Fin m => F ((start + 1) + (i : ℕ)) := by
      funext i
      congr 1
      rw [Fin.val_succ]
      omega
    rw [htail]
    have hrec := ih (start + 1) (fun r hr1 hr2 => h r (by omega) (by omega))
    have hend : start + 1 + m = start + (m + 1) := by omega
    rw [hend] at hrec
    rcases h start (le_refl _) (by omega) with ⟨hp, hadv⟩ | ⟨hp, hstat⟩
    · refine Absorb.adv (by simpa using hadv) ?_
      rw [← hp]
      exact hrec
    · refine Absorb.stat (by simpa using hstat) ?_
      rw [← hp]
      exact hrec

end Spine


section RaceOpt

variable (A : ChunkSystemB X s t 0 cB T pe mL)

/-- Additional prefix-length helper. -/
theorem preLen_le (C : ChunkSystemB X s t 0 cB T pe mL) (ωC : C.Ω)
    (idx : ℕ) : preLen C ωC idx ≤ (C.seq ωC).length :=
  take_flatten_le _ _

/-- The follow-the-survivor offline bound, survivor-abstracted: `SS` is
the survivor system with lift `ιS`, `CCs` the tail system with lift
`ιT`; the dead side enters only through the shapes of the coin chunks
(each of its requests contains the survivor's park). -/
theorem race_absorb_aux
    (SS CCs : ChunkSystemB X s t 0 cB T pe mL)
    (GmA GS GT : Set X → Set Y) (stopPt : Y) (κ : ℕ)
    (ιA ιS ιT : X → Y)
    (hιA : ∀ x y : X, dist (ιA x) (ιA y) ≤ dist x y)
    (hιS : ∀ x y : X, dist (ιS x) (ιS y) ≤ dist x y)
    (hιT : ∀ x y : X, dist (ιT x) (ιT y) ≤ dist x y)
    (hGA : ∀ S : Set X, ιA '' S ⊆ GmA S)
    (hGS : ∀ S : Set X, ιS '' S ⊆ GS S)
    (hGT : ∀ S : Set X, ιT '' S ⊆ GT S)
    (hJ1 : ιA t = ιS s) (hJ2 : ιS t = ιT s) (hJ3 : ιT t = stopPt)
    (ωA : A.Ω) (ωS : SS.Ω) (ωC : CCs.Ω)
    (cntS : ℕ → ℕ) (hS0 : cntS 0 = 0)
    (rem : ℕ) (hrem : cntS κ + rem = SS.m)
    (mtot : ℕ) (F : ℕ → List (Set Y))
    (hFA : ∀ r, r < A.m → F r = reqMap GmA (chunkN A ωA r))
    (hFcoin : ∀ j, j < κ →
      (cntS (j + 1) = cntS j + 1 ∧ ∃ Pk : Set Y,
        F (A.m + j) = parkMap GS Pk (chunkN SS ωS (cntS j)))
      ∨ (cntS (j + 1) = cntS j ∧
        ∀ Sy ∈ F (A.m + j), GS (lastXset SS ωS (cntS j)) ⊆ Sy))
    (hFrem : ∀ k, k < rem →
      F (A.m + κ + k) = reqMap GS (chunkN SS ωS (cntS κ + k)))
    (hFC : ∀ k, rem ≤ k → k - rem < CCs.m →
      F (A.m + κ + k) = reqMap GT (chunkN CCs ωC (k - rem)))
    (hFpad : ∀ k, rem + CCs.m ≤ k → A.m + κ + k < mtot →
      ∀ Sy ∈ F (A.m + κ + k), stopPt ∈ Sy) :
    evaderOfflineCost (ιA s)
      ((List.ofFn (fun i : Fin mtot => F (i : ℕ))).flatten)
      ≤ 3 * dist s t := by
  -- monotone consumption
  have hstep : ∀ j, j < κ →
      cntS (j + 1) = cntS j + 1 ∨ cntS (j + 1) = cntS j :=
    fun j hj => (hFcoin j hj).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hmono : ∀ b, b ≤ κ → ∀ a, a ≤ b → cntS a ≤ cntS b := by
    intro b
    induction b with
    | zero =>
      intro _ a ha
      have : a = 0 := by omega
      rw [this]
    | succ b ih =>
      intro hbκ a ha
      rcases Nat.lt_or_ge a (b + 1) with h1 | h1
      · have := ih (by omega) a (by omega)
        rcases hstep b (by omega) with h2 | h2 <;> omega
      · have : a = b + 1 := by omega
        rw [this]
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  have hδ3 : 0 < δ / 3 := by linarith
  obtain ⟨PA, hPA, hPAc⟩ := offline_exists_lt s (A.seq ωA)
    (lt_of_le_of_lt (A.hopt ωA) (by linarith : dist s t < dist s t + δ / 3))
  obtain ⟨PS, hPS, hPSc⟩ := offline_exists_lt s (SS.seq ωS)
    (lt_of_le_of_lt (SS.hopt ωS) (by linarith : dist s t < dist s t + δ / 3))
  obtain ⟨PT, hPT, hPTc⟩ := offline_exists_lt s (CCs.seq ωC)
    (lt_of_le_of_lt (CCs.hopt ωC) (by linarith : dist s t < dist s t + δ / 3))
  set nA := (A.seq ωA).length with hnA
  set nS := (SS.seq ωS).length with hnS
  set nC := (CCs.seq ωC).length with hnC
  have hnA1 : 0 < nA := seq_length_pos A ωA
  have hnS1 : 0 < nS := seq_length_pos SS ωS
  have hnC1 : 0 < nC := seq_length_pos CCs ωC
  have hAend : PA nA = t := serves_end A ωA hPA
  have hSend : PS nS = t := serves_end SS ωS hPS
  have hTend : PT nC = t := serves_end CCs ωC hPT
  set Q : ℕ → Y := fun i => if i < nA then ιA (PA i)
    else if i < nA + nS then ιS (PS (i - nA))
    else ιT (PT (i - nA - nS)) with hQdef
  have hQA : ∀ i, i ≤ nA → Q i = ιA (PA i) := by
    intro i hi
    rcases Nat.lt_or_ge i nA with h1 | h1
    · show (if i < nA then ιA (PA i) else _) = _
      rw [if_pos h1]
    · have he : i = nA := by omega
      rw [he]
      show (if nA < nA then ιA (PA nA)
        else if nA < nA + nS then ιS (PS (nA - nA))
        else ιT (PT (nA - nA - nS))) = ιA (PA nA)
      rw [if_neg (by omega), if_pos (by omega), Nat.sub_self, hPS.1,
        ← hJ1, hAend]
  have hQS : ∀ i, i ≤ nS → Q (nA + i) = ιS (PS i) := by
    intro i hi
    rcases Nat.lt_or_ge i nS with h1 | h1
    · show (if nA + i < nA then _
        else if nA + i < nA + nS then ιS (PS (nA + i - nA))
        else _) = _
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    · have he : i = nS := by omega
      rw [he]
      show (if nA + nS < nA then ιA (PA (nA + nS))
        else if nA + nS < nA + nS then ιS (PS (nA + nS - nA))
        else ιT (PT (nA + nS - nA - nS))) = ιS (PS nS)
      rw [if_neg (by omega), if_neg (by omega),
        show nA + nS - nA - nS = 0 from by omega, hPT.1, ← hJ2, hSend]
  have hQT : ∀ i, Q (nA + nS + i) = ιT (PT i) := by
    intro i
    show (if nA + nS + i < nA then _
      else if nA + nS + i < nA + nS then _
      else ιT (PT (nA + nS + i - nA - nS))) = _
    rw [if_neg (by omega), if_neg (by omega),
      show nA + nS + i - nA - nS = i from by omega]
  set p : ℕ → ℕ := fun r =>
    if r ≤ A.m then preLen A ωA r
    else if r ≤ A.m + κ then nA + preLen SS ωS (cntS (r - A.m))
    else if r - A.m - κ ≤ rem then
      nA + preLen SS ωS (cntS κ + (r - A.m - κ))
    else if r - A.m - κ ≤ rem + CCs.m then
      nA + nS + preLen CCs ωC (r - A.m - κ - rem)
    else nA + nS + nC with hpdef
  have hpA : ∀ r, r ≤ A.m → p r = preLen A ωA r := by
    intro r hr
    show (if r ≤ A.m then preLen A ωA r else _) = _
    rw [if_pos hr]
  have hpcoin : ∀ j, j ≤ κ → p (A.m + j) = nA + preLen SS ωS (cntS j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [Nat.add_zero, hpA A.m (le_refl _), preLen_m, hS0, preLen_zero,
        Nat.add_zero, ← hnA]
    · show (if A.m + j ≤ A.m then _
        else if A.m + j ≤ A.m + κ then
          nA + preLen SS ωS (cntS (A.m + j - A.m))
        else _) = _
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have hptail1 : ∀ k, k ≤ rem →
      p (A.m + κ + k) = nA + preLen SS ωS (cntS κ + k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [show A.m + κ + 0 = A.m + κ from rfl,
        show cntS κ + 0 = cntS κ from rfl]
      exact hpcoin κ (le_refl _)
    · show (if A.m + κ + k ≤ A.m then _
        else if A.m + κ + k ≤ A.m + κ then _
        else if A.m + κ + k - A.m - κ ≤ rem then
          nA + preLen SS ωS (cntS κ + (A.m + κ + k - A.m - κ))
        else _) = _
      rw [if_neg (by omega), if_neg (by omega)]
      rw [show A.m + κ + k - A.m - κ = k from by omega, if_pos (by omega)]
  have hptail2 : ∀ k, rem ≤ k → k ≤ rem + CCs.m →
      p (A.m + κ + k) = nA + nS + preLen CCs ωC (k - rem) := by
    intro k hk1 hk2
    rcases Nat.eq_or_lt_of_le hk1 with h0 | h0
    · rw [← h0, hptail1 rem (le_refl _), hrem, preLen_m, Nat.sub_self,
        preLen_zero, Nat.add_zero, ← hnS]
    · show (if A.m + κ + k ≤ A.m then _
        else if A.m + κ + k ≤ A.m + κ then _
        else if A.m + κ + k - A.m - κ ≤ rem then _
        else if A.m + κ + k - A.m - κ ≤ rem + CCs.m then
          nA + nS + preLen CCs ωC (A.m + κ + k - A.m - κ - rem)
        else _) = _
      rw [if_neg (by omega), if_neg (by omega)]
      rw [show A.m + κ + k - A.m - κ = k from by omega, if_neg (by omega),
        if_pos (by omega)]
  have hptail3 : ∀ k, rem + CCs.m ≤ k →
      p (A.m + κ + k) = nA + nS + nC := by
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with h0 | h0
    · rw [← h0, hptail2 (rem + CCs.m) (by omega) (le_refl _),
        Nat.add_sub_cancel_left, preLen_m, ← hnC]
    · show (if A.m + κ + k ≤ A.m then _
        else if A.m + κ + k ≤ A.m + κ then _
        else if A.m + κ + k - A.m - κ ≤ rem then _
        else if A.m + κ + k - A.m - κ ≤ rem + CCs.m then _
        else nA + nS + nC) = _
      rw [if_neg (by omega), if_neg (by omega)]
      rw [show A.m + κ + k - A.m - κ = k from by omega, if_neg (by omega),
        if_neg (by omega)]
  -- the per-index certificates
  have hcert : ∀ r, 0 ≤ r → r < 0 + mtot →
      (p (r + 1) = p r + (F r).length ∧
        ∀ n : ℕ, ∀ hn : n < (F r).length,
          ((F r)[n]'hn).Nonempty → Q (p r + n + 1) ∈ (F r)[n]'hn)
      ∨ (p (r + 1) = p r ∧ ∀ S ∈ F r, S.Nonempty → Q (p r) ∈ S) := by
    intro r hr0 hrm
    by_cases hr1 : r < A.m
    · -- phase A: advance
      left
      have hF := hFA r hr1
      have hlen : (F r).length = (chunkN A ωA r).length := by
        rw [hF]; unfold reqMap; rw [List.length_map]
      constructor
      · rw [hpA r (by omega), hpA (r + 1) (by omega),
          preLen_succ A ωA hr1, hlen]
      · intro n hn hne
        have hn2 : n < (chunkN A ωA r).length := by omega
        have hq : (F r)[n]? = (GmA ((chunkN A ωA r)[n]'hn2)) := by
          rw [hF]
          unfold reqMap
          rw [List.getElem?_map, List.getElem?_eq_getElem hn2]
          rfl
        have hget : (F r)[n]'hn = GmA ((chunkN A ωA r)[n]'hn2) := by
          rw [List.getElem?_eq_getElem hn] at hq
          exact Option.some_injective _ hq
        rw [hget]
        have hcne : ((chunkN A ωA r)[n]'hn2).Nonempty := by
          refine A.hne ωA ⟨r, hr1⟩ _ ?_
          rw [← chunkN_lt A ωA hr1]
          exact List.getElem_mem _
        have hserve := serves_chunk_pos A ωA hPA hr1 hn2 hcne
        have hidx : preLen A ωA r + n + 1 ≤ nA := by
          have h1 : preLen A ωA (r + 1)
              = preLen A ωA r + (chunkN A ωA r).length :=
            preLen_succ A ωA hr1
          have h2 := preLen_le A ωA (r + 1)
          omega
        rw [hpA r (by omega), hQA _ hidx]
        exact hGA _ ⟨_, hserve, rfl⟩
    · rw [not_lt] at hr1
      by_cases hr2 : r < A.m + κ
      · -- coin phase
        obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
        have hj : j < κ := by omega
        rcases hFcoin j hj with ⟨hc1, Pk, hF⟩ | ⟨hc1, hstat⟩
        · -- survivor active: advance
          left
          have hjm : cntS j + 1 ≤ cntS κ := by
            rw [← hc1]
            exact hmono κ (le_refl _) (j + 1) (by omega)
          have hjm2 : cntS j < SS.m := by omega
          have hlen : (F (A.m + j)).length
              = (chunkN SS ωS (cntS j)).length := by
            rw [hF]; unfold parkMap; rw [List.length_map]
          constructor
          · rw [show A.m + j + 1 = A.m + (j + 1) from rfl,
              hpcoin (j + 1) (by omega), hpcoin j (by omega), hc1,
              preLen_succ SS ωS hjm2, hlen]
            omega
          · intro n hn hne
            have hn2 : n < (chunkN SS ωS (cntS j)).length := by omega
            have hq : (F (A.m + j))[n]?
                = (GS ((chunkN SS ωS (cntS j))[n]'hn2) ∪ Pk) := by
              rw [hF]
              unfold parkMap
              rw [List.getElem?_map, List.getElem?_eq_getElem hn2]
              rfl
            have hget : (F (A.m + j))[n]'hn
                = GS ((chunkN SS ωS (cntS j))[n]'hn2) ∪ Pk := by
              rw [List.getElem?_eq_getElem hn] at hq
              exact Option.some_injective _ hq
            rw [hget]
            have hcne : ((chunkN SS ωS (cntS j))[n]'hn2).Nonempty := by
              refine SS.hne ωS ⟨cntS j, hjm2⟩ _ ?_
              rw [← chunkN_lt SS ωS hjm2]
              exact List.getElem_mem _
            have hserve := serves_chunk_pos SS ωS hPS hjm2 hn2 hcne
            have hidx : preLen SS ωS (cntS j) + n + 1 ≤ nS := by
              have h1 : preLen SS ωS (cntS j + 1)
                  = preLen SS ωS (cntS j)
                    + (chunkN SS ωS (cntS j)).length :=
                preLen_succ SS ωS hjm2
              have h2 := preLen_le SS ωS (cntS j + 1)
              omega
            rw [hpcoin j (by omega)]
            rw [show nA + preLen SS ωS (cntS j) + n + 1
              = nA + (preLen SS ωS (cntS j) + n + 1) from by omega]
            rw [hQS _ hidx]
            exact Set.mem_union_left _ (hGS _ ⟨_, hserve, rfl⟩)
        · -- dead active: stationary
          right
          constructor
          · rw [show A.m + j + 1 = A.m + (j + 1) from rfl,
              hpcoin (j + 1) (by omega), hpcoin j (by omega), hc1]
          · intro S hS hSne
            have hidx : preLen SS ωS (cntS j) ≤ nS := preLen_le SS ωS _
            have hpos := serves_last_pos SS ωS hPS (cntS j)
            rw [hpcoin j (by omega), hQS _ hidx]
            exact hstat S hS (hGS _ ⟨_, hpos, rfl⟩)
      · -- tail
        rw [not_lt] at hr2
        obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
        have hSκm : cntS κ ≤ SS.m := by omega
        by_cases hk1 : k < rem
        · -- survivor remainder: advance
          left
          have hF := hFrem k hk1
          have hjm2 : cntS κ + k < SS.m := by omega
          have hlen : (F (A.m + κ + k)).length
              = (chunkN SS ωS (cntS κ + k)).length := by
            rw [hF]; unfold reqMap; rw [List.length_map]
          constructor
          · rw [show A.m + κ + k + 1 = A.m + κ + (k + 1) from rfl,
              hptail1 (k + 1) (by omega), hptail1 k (by omega),
              show cntS κ + (k + 1) = (cntS κ + k) + 1 from rfl,
              preLen_succ SS ωS hjm2, hlen]
            omega
          · intro n hn hne
            have hn2 : n < (chunkN SS ωS (cntS κ + k)).length := by omega
            have hq : (F (A.m + κ + k))[n]?
                = (GS ((chunkN SS ωS (cntS κ + k))[n]'hn2)) := by
              rw [hF]
              unfold reqMap
              rw [List.getElem?_map, List.getElem?_eq_getElem hn2]
              rfl
            have hget : (F (A.m + κ + k))[n]'hn
                = GS ((chunkN SS ωS (cntS κ + k))[n]'hn2) := by
              rw [List.getElem?_eq_getElem hn] at hq
              exact Option.some_injective _ hq
            rw [hget]
            have hcne : ((chunkN SS ωS (cntS κ + k))[n]'hn2).Nonempty := by
              refine SS.hne ωS ⟨cntS κ + k, hjm2⟩ _ ?_
              rw [← chunkN_lt SS ωS hjm2]
              exact List.getElem_mem _
            have hserve := serves_chunk_pos SS ωS hPS hjm2 hn2 hcne
            have hidx : preLen SS ωS (cntS κ + k) + n + 1 ≤ nS := by
              have h1 : preLen SS ωS (cntS κ + k + 1)
                  = preLen SS ωS (cntS κ + k)
                    + (chunkN SS ωS (cntS κ + k)).length :=
                preLen_succ SS ωS hjm2
              have h2 := preLen_le SS ωS (cntS κ + k + 1)
              omega
            rw [hptail1 k (by omega)]
            rw [show nA + preLen SS ωS (cntS κ + k) + n + 1
              = nA + (preLen SS ωS (cntS κ + k) + n + 1) from by omega]
            rw [hQS _ hidx]
            exact hGS _ ⟨_, hserve, rfl⟩
        · rw [not_lt] at hk1
          by_cases hk2 : k - rem < CCs.m
          · -- tail system: advance
            left
            have hF := hFC k hk1 hk2
            have hlen : (F (A.m + κ + k)).length
                = (chunkN CCs ωC (k - rem)).length := by
              rw [hF]; unfold reqMap; rw [List.length_map]
            constructor
            · rw [show A.m + κ + k + 1 = A.m + κ + (k + 1) from rfl,
                hptail2 (k + 1) (by omega) (by omega),
                hptail2 k (by omega) (by omega),
                show k + 1 - rem = (k - rem) + 1 from by omega,
                preLen_succ CCs ωC hk2, hlen]
              omega
            · intro n hn hne
              have hn2 : n < (chunkN CCs ωC (k - rem)).length := by omega
              have hq : (F (A.m + κ + k))[n]?
                  = (GT ((chunkN CCs ωC (k - rem))[n]'hn2)) := by
                rw [hF]
                unfold reqMap
                rw [List.getElem?_map, List.getElem?_eq_getElem hn2]
                rfl
              have hget : (F (A.m + κ + k))[n]'hn
                  = GT ((chunkN CCs ωC (k - rem))[n]'hn2) := by
                rw [List.getElem?_eq_getElem hn] at hq
                exact Option.some_injective _ hq
              rw [hget]
              have hcne : ((chunkN CCs ωC (k - rem))[n]'hn2).Nonempty := by
                refine CCs.hne ωC ⟨k - rem, hk2⟩ _ ?_
                rw [← chunkN_lt CCs ωC hk2]
                exact List.getElem_mem _
              have hserve := serves_chunk_pos CCs ωC hPT hk2 hn2 hcne
              rw [hptail2 k (by omega) (by omega)]
              rw [show nA + nS + preLen CCs ωC (k - rem) + n + 1
                = nA + nS + (preLen CCs ωC (k - rem) + n + 1) from by omega]
              rw [hQT _]
              exact hGT _ ⟨_, hserve, rfl⟩
          · -- padding: stationary
            rw [not_lt] at hk2
            right
            constructor
            · rw [show A.m + κ + k + 1 = A.m + κ + (k + 1) from rfl,
                hptail3 (k + 1) (by omega), hptail3 k (by omega)]
            · intro S hS hSne
              have hpadk := hFpad k (by omega) (by omega) S hS
              rw [hptail3 k (by omega), hQT nC, hTend, hJ3]
              exact hpadk
  -- assemble
  have habs := absorb_build Q F p mtot 0 hcert
  have hofn : (fun i : Fin mtot => F (0 + (i : ℕ)))
      = fun i : Fin mtot => F (i : ℕ) := by
    funext i
    rw [Nat.zero_add]
  rw [hofn, Nat.zero_add] at habs
  have hbound := habs.offline_le
  have hp0 : p 0 = 0 := by
    rw [hpA 0 (by omega), preLen_zero]
  have hQ0 : Q (p 0) = ιA s := by
    rw [hp0, hQA 0 (by omega), hPA.1]
  rw [hQ0] at hbound
  refine le_trans hbound ?_
  have hpm : p mtot ≤ nA + nS + nC := by
    show (if mtot ≤ A.m then preLen A ωA mtot
      else if mtot ≤ A.m + κ then nA + preLen SS ωS (cntS (mtot - A.m))
      else if mtot - A.m - κ ≤ rem then
        nA + preLen SS ωS (cntS κ + (mtot - A.m - κ))
      else if mtot - A.m - κ ≤ rem + CCs.m then
        nA + nS + preLen CCs ωC (mtot - A.m - κ - rem)
      else nA + nS + nC) ≤ nA + nS + nC
    by_cases h1 : mtot ≤ A.m
    · rw [if_pos h1]
      have h2 := preLen_le A ωA mtot
      omega
    · rw [if_neg h1]
      by_cases h2 : mtot ≤ A.m + κ
      · rw [if_pos h2]
        have h3 := preLen_le SS ωS (cntS (mtot - A.m))
        omega
      · rw [if_neg h2]
        by_cases h3 : mtot - A.m - κ ≤ rem
        · rw [if_pos h3]
          have h4 := preLen_le SS ωS (cntS κ + (mtot - A.m - κ))
          omega
        · rw [if_neg h3]
          by_cases h4 : mtot - A.m - κ ≤ rem + CCs.m
          · rw [if_pos h4]
            have h5 := preLen_le CCs ωC (mtot - A.m - κ - rem)
            omega
          · rw [if_neg h4]
  have hsub : ∑ i ∈ Finset.Ico 0 (p mtot), dist (Q i) (Q (i + 1))
      ≤ ∑ i ∈ Finset.Ico 0 (nA + nS + nC), dist (Q i) (Q (i + 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico (le_refl _) hpm)
      (fun i _ _ => dist_nonneg)
  refine le_trans hsub ?_
  rw [← Finset.sum_Ico_consecutive (fun i => dist (Q i) (Q (i + 1)))
      (by omega : 0 ≤ nA + nS) (by omega : nA + nS ≤ nA + nS + nC),
    ← Finset.sum_Ico_consecutive (fun i => dist (Q i) (Q (i + 1)))
      (by omega : 0 ≤ nA) (by omega : nA ≤ nA + nS)]
  have hcost1 : ∑ i ∈ Finset.Ico 0 nA, dist (Q i) (Q (i + 1))
      ≤ ∑ j ∈ Finset.range nA, dist (PA j) (PA (j + 1)) := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [hQA i (by omega), hQA (i + 1) (by omega)]
    exact hιA _ _
  have hcost2 : ∑ i ∈ Finset.Ico nA (nA + nS), dist (Q i) (Q (i + 1))
      ≤ ∑ j ∈ Finset.range nS, dist (PS j) (PS (j + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hQS i (by omega), show nA + i + 1 = nA + (i + 1) from rfl,
      hQS (i + 1) (by omega)]
    exact hιS _ _
  have hcost3 : ∑ i ∈ Finset.Ico (nA + nS) (nA + nS + nC),
      dist (Q i) (Q (i + 1))
      ≤ ∑ j ∈ Finset.range nC, dist (PT j) (PT (j + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hQT i, show nA + nS + i + 1 = nA + nS + (i + 1) from rfl,
      hQT (i + 1)]
    exact hιT _ _
  have htot := add_le_add (add_le_add hcost1 hcost2) hcost3
  linarith

end RaceOpt



section RaceWrap

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ)

/-- The race offline bound: follow the survivor. -/
theorem race_opt (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (ιA ιL ιR ιTL ιTR : X → Y)
    (hιA : ∀ x y : X, dist (ιA x) (ιA y) ≤ dist x y)
    (hιL : ∀ x y : X, dist (ιL x) (ιL y) ≤ dist x y)
    (hιR : ∀ x y : X, dist (ιR x) (ιR y) ≤ dist x y)
    (hιTL : ∀ x y : X, dist (ιTL x) (ιTL y) ≤ dist x y)
    (hιTR : ∀ x y : X, dist (ιTR x) (ιTR y) ≤ dist x y)
    (hGA : ∀ S : Set X, ιA '' S ⊆ GmA S)
    (hGL : ∀ S : Set X, ιL '' S ⊆ GmL S)
    (hGR : ∀ S : Set X, ιR '' S ⊆ GmR S)
    (hGTL : ∀ S : Set X, ιTL '' S ⊆ GmTL S)
    (hGTR : ∀ S : Set X, ιTR '' S ⊆ GmTR S)
    (hJ1L : ιA t = ιL s) (hJ1R : ιA t = ιR s)
    (hJ2L : ιL t = ιTL s) (hJ2R : ιR t = ιTR s)
    (hJ3L : ιTL t = stopPt) (hJ3R : ιTR t = stopPt)
    (ω : RΩ A BL BR CC κ) :
    evaderOfflineCost (ιA s)
      ((List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
        rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).flatten)
      ≤ 3 * dist s t := by
  have hcmL : cntL ω.2.2.2.2 κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  have hcmR : cntR ω.2.2.2.2 κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  by_cases hs : survL A BL BR CC κ ω
  · -- survivor is the left side
    have hremv : remCnt A BL BR CC κ ω = BL.m - cntL ω.2.2.2.2 κ := by
      unfold remCnt; rw [if_pos hs]
    refine race_absorb_aux A BL CC GmA GmL GmTL stopPt κ ιA ιL ιTL
      hιA hιL hιTL hGA hGL hGTL hJ1L hJ2L hJ3L ω.1 ω.2.1 ω.2.2.2.1
      (cntL ω.2.2.2.2) (cntL_zero _)
      (remCnt A BL BR CC κ ω) (by omega)
      (mrace A BL BR CC κ)
      (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω)
      ?_ ?_ ?_ ?_ ?_
    · intro r hr
      exact rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr
    · intro j hj
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj]
      by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
      · left
        refine ⟨by rw [cntL_succ _ hj, if_pos hb],
          parkR A BL BR CC GmR κ ω j, ?_⟩
        rw [if_pos hb]
      · right
        refine ⟨by rw [cntL_succ _ hj, if_neg hb, Nat.add_zero], ?_⟩
        intro Sy hSy
        rw [if_neg hb] at hSy
        unfold parkMap at hSy
        rw [List.mem_map] at hSy
        obtain ⟨S', hS', rfl⟩ := hSy
        show parkL A BL BR CC GmL κ ω j ⊆ _
        exact Set.subset_union_right
    · intro k hk
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_pos hs, if_pos hk]
    · intro k hk1 hk2
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_pos hs, if_neg (by omega), if_pos hk2]
    · intro k hk1 hk2 Sy hSy
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_pos hs, if_neg (by omega), if_neg (by omega)] at hSy
      rw [List.mem_singleton] at hSy
      rw [hSy]
      exact rfl
  · -- survivor is the right side
    have hremv : remCnt A BL BR CC κ ω = BR.m - cntR ω.2.2.2.2 κ := by
      unfold remCnt; rw [if_neg hs]
    refine race_absorb_aux A BR CC GmA GmR GmTR stopPt κ ιA ιR ιTR
      hιA hιR hιTR hGA hGR hGTR hJ1R hJ2R hJ3R ω.1 ω.2.2.1 ω.2.2.2.1
      (cntR ω.2.2.2.2) (cntR_zero _)
      (remCnt A BL BR CC κ ω) (by omega)
      (mrace A BL BR CC κ)
      (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω)
      ?_ ?_ ?_ ?_ ?_
    · intro r hr
      exact rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr
    · intro j hj
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj]
      by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
      · right
        refine ⟨by rw [cntR_succ _ hj, if_neg (by simpa using hb),
          Nat.add_zero], ?_⟩
        intro Sy hSy
        rw [if_pos hb] at hSy
        unfold parkMap at hSy
        rw [List.mem_map] at hSy
        obtain ⟨S', hS', rfl⟩ := hSy
        show parkR A BL BR CC GmR κ ω j ⊆ _
        exact Set.subset_union_right
      · left
        refine ⟨by rw [cntR_succ _ hj, if_pos (by simpa using hb)],
          parkL A BL BR CC GmL κ ω j, ?_⟩
        rw [if_neg hb]
    · intro k hk
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_neg hs, if_pos hk]
    · intro k hk1 hk2
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_neg hs, if_neg (by omega), if_pos hk2]
    · intro k hk1 hk2 Sy hSy
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_neg hs, if_neg (by omega), if_neg (by omega)] at hSy
      rw [List.mem_singleton] at hSy
      rw [hSy]
      exact rfl

/-- Every request of the race is nonempty. -/
theorem race_ne
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (ω : RΩ A BL BR CC κ) (r : ℕ) :
    ∀ S ∈ rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r,
      S.Nonempty := by
  have hchunkN : ∀ (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
      (idx : ℕ) (S' : Set X), S' ∈ chunkN C ωc idx → S'.Nonempty := by
    intro C ωc idx S' hS'
    by_cases hidx : idx < C.m
    · rw [chunkN_lt C ωc hidx] at hS'
      exact C.hne ωc _ _ hS'
    · rw [chunkN_ge C ωc (by omega)] at hS'
      simp at hS'
  intro S hS
  by_cases hr1 : r < A.m
  · rw [rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr1] at hS
    unfold reqMap at hS
    rw [List.mem_map] at hS
    obtain ⟨S', hS', rfl⟩ := hS
    exact hGneA _ (hchunkN A ω.1 r S' hS')
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      have hj : j < κ := by omega
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj] at hS
      by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
      · rw [if_pos hb] at hS
        unfold parkMap at hS
        rw [List.mem_map] at hS
        obtain ⟨S', hS', rfl⟩ := hS
        exact Set.Nonempty.inl (hGneL _ (hchunkN BL ω.2.1 _ S' hS'))
      · rw [if_neg hb] at hS
        unfold parkMap at hS
        rw [List.mem_map] at hS
        obtain ⟨S', hS', rfl⟩ := hS
        exact Set.Nonempty.inl (hGneR _ (hchunkN BR ω.2.2.1 _ S' hS'))
    · rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k] at hS
      by_cases hsv : survL A BL BR CC κ ω
      · rw [if_pos hsv] at hS
        by_cases hk1 : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk1] at hS
          unfold reqMap at hS
          rw [List.mem_map] at hS
          obtain ⟨S', hS', rfl⟩ := hS
          exact hGneL _ (hchunkN BL ω.2.1 _ S' hS')
        · rw [if_neg hk1] at hS
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2] at hS
            unfold reqMap at hS
            rw [List.mem_map] at hS
            obtain ⟨S', hS', rfl⟩ := hS
            exact hGneTL _ (hchunkN CC ω.2.2.2.1 _ S' hS')
          · rw [if_neg hk2, List.mem_singleton] at hS
            rw [hS]
            exact ⟨stopPt, rfl⟩
      · rw [if_neg hsv] at hS
        by_cases hk1 : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk1] at hS
          unfold reqMap at hS
          rw [List.mem_map] at hS
          obtain ⟨S', hS', rfl⟩ := hS
          exact hGneR _ (hchunkN BR ω.2.2.1 _ S' hS')
        · rw [if_neg hk1] at hS
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2] at hS
            unfold reqMap at hS
            rw [List.mem_map] at hS
            obtain ⟨S', hS', rfl⟩ := hS
            exact hGneTR _ (hchunkN CC ω.2.2.2.1 _ S' hS')
          · rw [if_neg hk2, List.mem_singleton] at hS
            rw [hS]
            exact ⟨stopPt, rfl⟩

end RaceWrap



section RaceLast

variable {β : Type*}

theorem ofFn_cast (F : ℕ → β) {m n : ℕ} (h : m = n) :
    List.ofFn (fun i : Fin m => F (i : ℕ))
      = List.ofFn (fun i : Fin n => F (i : ℕ)) := by
  subst h
  rfl

theorem ofFn_split (F : ℕ → β) (m1 m2 : ℕ) :
    List.ofFn (fun i : Fin (m1 + m2) => F (i : ℕ))
      = List.ofFn (fun i : Fin m1 => F (i : ℕ))
        ++ List.ofFn (fun i : Fin m2 => F (m1 + (i : ℕ))) := by
  rw [List.ofFn_add]
  congr 1
  all_goals
    first
      | (exact congrArg List.ofFn (funext fun i => by congr 1; simp))
      | (funext i; congr 1; simp)
      | simp

theorem flatten_pad (n : ℕ) (x : β) :
    (List.ofFn (fun _ : Fin n => [x])).flatten = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, ih, List.replicate_succ]
    rfl

theorem getLast?_replicate_pos {n : ℕ} (hn : 0 < n) (x : β) :
    (List.replicate n x).getLast? = some x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ', List.getLast?_concat]

theorem flatten_map_chunks {γ δ : Type*} (G : γ → δ) (cs : List (List γ)) :
    (List.map (List.map G) cs).flatten = List.map G cs.flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.flatten_cons, List.flatten_cons,
      List.map_append, ih]

theorem ofFn_map_chunks {γ δ : Type*} (G : γ → δ) {n : ℕ}
    (f : Fin n → List γ) :
    List.ofFn (fun i => List.map G (f i))
      = List.map (List.map G) (List.ofFn f) := by
  rw [List.map_ofFn]
  rfl

theorem getLast?_map' {γ δ : Type*} (G : γ → δ) (l : List γ) :
    (List.map G l).getLast? = l.getLast?.map G := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.length_map,
    List.getElem?_map]

end RaceLast

section RaceLastMain

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ)

/-- The race sequence ends pinned at the stopping point. -/
theorem race_last
    (hTLt : GmTL {t} = {stopPt}) (hTRt : GmTR {t} = {stopPt})
    (ω : RΩ A BL BR CC κ) :
    ((List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
      rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
        (i : ℕ))).flatten).getLast? = some {stopPt} := by
  set F := rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω with hF
  set rem := remCnt A BL BR CC κ ω with hrem
  have hremmax : rem ≤ max BL.m BR.m := remCnt_le_max A BL BR CC κ ω
  set pad := max BL.m BR.m - rem with hpad
  have hm : mrace A BL BR CC κ = ((A.m + κ + rem) + CC.m) + pad := by
    unfold mrace
    omega
  rw [ofFn_cast F hm, ofFn_split F ((A.m + κ + rem) + CC.m) pad,
    List.flatten_append]
  by_cases hp : 0 < pad
  · -- padding present: the last chunk is [{stopPt}]
    have hpadchunks :
        List.ofFn (fun i : Fin pad => F ((A.m + κ + rem) + CC.m + (i : ℕ)))
          = List.ofFn (fun _ : Fin pad => [({stopPt} : Set Y)]) := by
      congr 1
      funext i
      rw [show (A.m + κ + rem) + CC.m + (i : ℕ)
        = A.m + κ + (rem + CC.m + (i : ℕ)) from by omega, hF,
        rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
          (rem + CC.m + (i : ℕ))]
      by_cases hsv : survL A BL BR CC κ ω
      · rw [if_pos hsv, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hsv, if_neg (by omega), if_neg (by omega)]
    rw [hpadchunks, flatten_pad]
    rw [List.getLast?_append_of_ne_nil _ (by
      intro hcon
      have hlc := congrArg List.length hcon
      rw [List.length_replicate] at hlc
      simp at hlc
      omega)]
    exact getLast?_replicate_pos hp _
  · -- no padding: the last chunk list is the mapped tail system
    have hpz : pad = 0 := by omega
    rw [hpz]
    rw [show (List.ofFn (fun i : Fin 0 =>
      F ((A.m + κ + rem) + CC.m + (i : ℕ)))) = [] from rfl]
    rw [List.flatten_nil, List.append_nil]
    rw [ofFn_split F (A.m + κ + rem) CC.m, List.flatten_append]
    by_cases hsv : survL A BL BR CC κ ω
    · have hccchunks :
          List.ofFn (fun i : Fin CC.m => F ((A.m + κ + rem) + (i : ℕ)))
            = List.ofFn (fun i : Fin CC.m =>
                List.map GmTL (CC.chunk ω.2.2.2.1 i)) := by
        congr 1
        funext i
        rw [show (A.m + κ + rem) + (i : ℕ)
          = A.m + κ + (rem + (i : ℕ)) from by omega, hF,
          rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (rem + (i : ℕ))]
        rw [if_pos hsv, if_neg (by omega),
          show rem + (i : ℕ) - rem = (i : ℕ) from by omega,
          if_pos i.isLt]
        unfold reqMap
        rw [chunkN_lt CC ω.2.2.2.1 i.isLt]
      rw [hccchunks, ofFn_map_chunks, flatten_map_chunks]
      have hne : List.map GmTL ((List.ofFn (CC.chunk ω.2.2.2.1)).flatten)
          ≠ [] := by
        rw [ne_eq, List.map_eq_nil_iff]
        intro hcon
        have h2 := seq_length_pos CC ω.2.2.2.1
        unfold ChunkSystemB.seq at h2
        rw [hcon] at h2
        simp at h2
      rw [List.getLast?_append_of_ne_nil _ hne, getLast?_map',
        CC.hlast ω.2.2.2.1]
      rw [Option.map_some]
      rw [hTLt]
    · have hccchunks :
          List.ofFn (fun i : Fin CC.m => F ((A.m + κ + rem) + (i : ℕ)))
            = List.ofFn (fun i : Fin CC.m =>
                List.map GmTR (CC.chunk ω.2.2.2.1 i)) := by
        congr 1
        funext i
        rw [show (A.m + κ + rem) + (i : ℕ)
          = A.m + κ + (rem + (i : ℕ)) from by omega, hF,
          rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (rem + (i : ℕ))]
        rw [if_neg hsv, if_neg (by omega),
          show rem + (i : ℕ) - rem = (i : ℕ) from by omega,
          if_pos i.isLt]
        unfold reqMap
        rw [chunkN_lt CC ω.2.2.2.1 i.isLt]
      rw [hccchunks, ofFn_map_chunks, flatten_map_chunks]
      have hne : List.map GmTR ((List.ofFn (CC.chunk ω.2.2.2.1)).flatten)
          ≠ [] := by
        rw [ne_eq, List.map_eq_nil_iff]
        intro hcon
        have h2 := seq_length_pos CC ω.2.2.2.1
        unfold ChunkSystemB.seq at h2
        rw [hcon] at h2
        simp at h2
      rw [List.getLast?_append_of_ne_nil _ hne, getLast?_map',
        CC.hlast ω.2.2.2.1]
      rw [Option.map_some]
      rw [hTRt]

end RaceLastMain


end Race

end KServer


