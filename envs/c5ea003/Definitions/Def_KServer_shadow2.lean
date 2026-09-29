-- Prove2me | Definitions.Def_KServer_shadow2
-- name    : KServer_shadow2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T15:34:50.771732+00:00
-- url     : https://prove2.me/theorems/b106b081-9a91-44bb-89bf-4a5274ac254a
-- title:
--   Offset shadow evaders for interleaved premises
-- statement:
--   In the BCR race, a side system's chunks are interleaved with material from other phases, so a level-$w$ cost premise for one chunk must be instantiated with an induced evader that ignores the side history — whose image in the race is already part of the fixed foreign prefix — and shadows the step evader on the current chunk only. The offset shadows $\mathrm{shadowFrom}_n$ and $\mathrm{parkShadowFrom}_n$ drop the first $n$ requests of their input before mapping; on side histories of length exactly $n$, with the aligned-start condition that the shadow's position after the history is the projection of the evader's current position, their chunk costs and bail-aware costs are dominated by the evader's on the transformed chunk alone: $$\mathrm{bailCost}_{\mathrm{shadow}}(h, \chi, p_e) \le \mathrm{bailCost}_{E}(h_0, \theta(\chi), p'),$$ for the transported bail rule (united with the first parked position in the park-aware case). The park bail is financed by the separation between the transformed requests and the parking set, which must exceed the diameter of the small space plus the escape price. These are the exact instantiations used for every phase premise of the race: plain offset shadows for the union and tail phases, park-aware offset shadows for the coin phase.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

/-! ### Offset shadow evaders

In the race, a side system's chunks are interleaved with other phases'
material, so the level-`w` premise for one chunk must be instantiated
with an induced evader that ignores the side history (whose image in the
race is already part of the fixed foreign prefix) and shadows the step
evader on the current chunk only.  `shadowFrom`/`parkShadowFrom` drop the
first `n` requests of their input before mapping; on histories of length
exactly `n` they behave like chunk-only shadows. -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

open Classical in
/-- The offset shadow: serve short histories by choice, shadow the mapped
remainder beyond the offset. -/
noncomputable def shadowFrom (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) : EvaderAlgorithm X where
  pos l :=
    if l.length ≤ n then
      match l.getLast? with
      | some S =>
          if π (E.pos (h₀ ++ reqMap G (l.drop n))) ∈ S then
            π (E.pos (h₀ ++ reqMap G (l.drop n)))
          else if hS : S.Nonempty then hS.choose
          else π (E.pos (h₀ ++ reqMap G (l.drop n)))
      | none => π (E.pos (h₀ ++ reqMap G (l.drop n)))
    else π (E.pos (h₀ ++ reqMap G (l.drop n)))
  serves l S hS := by
    by_cases hlen : (l ++ [S]).length ≤ n
    · have hlast : (l ++ [S]).getLast? = some S := List.getLast?_concat
      simp only [hlen, if_pos, hlast]
      by_cases hmem : π (E.pos (h₀ ++ reqMap G ((l ++ [S]).drop n))) ∈ S
      · rw [if_pos hmem]
        exact hmem
      · rw [if_neg hmem, dif_pos hS]
        exact hS.choose_spec
    · simp only [hlen, if_neg, not_false_iff]
      have hlen2 : n ≤ l.length := by
        have h1 : (l ++ [S]).length = l.length + 1 := by simp
        omega
      have hdrop : (l ++ [S]).drop n = l.drop n ++ [S] :=
        List.drop_append_of_le_length hlen2
      rw [hdrop, reqMap_append, ← List.append_assoc]
      exact hG S _ (E.serves _ _ (hGne S hS))

theorem drop_exact {α : Type*} {h l : List α} {n : ℕ} (hh : h.length = n) :
    (h ++ l).drop n = l := by
  rw [← hh, List.drop_left]

open Classical in
theorem shadowFrom_pos (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h l : List (Set X)}
    (hh : h.length = n) (hl : l ≠ []) :
    (shadowFrom n π G hG hGne E h₀).pos (h ++ l)
      = π (E.pos (h₀ ++ reqMap G l)) := by
  have hlen : ¬ (h ++ l).length ≤ n := by
    have h1 : (h ++ l).length = h.length + l.length := by simp
    have h2 : 0 < l.length := List.length_pos_iff.mpr hl
    omega
  unfold shadowFrom
  simp only [hlen, if_neg, not_false_iff]
  rw [drop_exact hh]

/-- Chunk-only cost domination for the offset shadow with aligned start. -/
theorem shadowFrom_costOn_le (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) (h χ : List (Set X))
    (hh : h.length = n)
    (hstart : (shadowFrom n π G hG hGne E h₀).pos h = π (E.pos h₀)) :
    (shadowFrom n π G hG hGne E h₀).costOn h χ
      ≤ E.costOn h₀ (reqMap G χ) := by
  induction χ using List.reverseRecOn with
  | nil =>
    have h1 : (shadowFrom n π G hG hGne E h₀).costOn h [] = 0 := by
      unfold EvaderAlgorithm.costOn
      rw [List.append_nil, sub_self]
    rw [h1]
    exact E.costOn_nonneg h₀ (reqMap G [])
  | append_singleton χ S ih =>
    rw [EvaderAlgorithm.costOn_concat, reqMap_append,
      show reqMap G [S] = [G S] from rfl, EvaderAlgorithm.costOn_concat]
    rcases List.eq_nil_or_concat χ with rfl | ⟨χ', S', rfl⟩
    · -- single-request chunk: one step from the offset position
      have hre : reqMap G ([] : List (Set X)) = [] := rfl
      simp only [hre, List.append_nil]
      have hnil : (shadowFrom n π G hG hGne E h₀).costOn h [] = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil, sub_self]
      have hnil2 : E.costOn h₀ ([] : List (Set Y)) = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil, sub_self]
      have hpos1 : (shadowFrom n π G hG hGne E h₀).pos (h ++ [S])
          = π (E.pos (h₀ ++ [G S])) := by
        have := shadowFrom_pos n π G hG hGne E h₀ hh
          (l := [S]) (by simp)
        rwa [show reqMap G [S] = [G S] from rfl] at this
      rw [hnil, hnil2, hpos1, hstart]
      have hlip := hπ (E.pos h₀) (E.pos (h₀ ++ [G S]))
      linarith
    · -- longer chunk: both endpoints are genuine shadows
      simp only [List.concat_eq_append]
      have hpos1 : (shadowFrom n π G hG hGne E h₀).pos (h ++ (χ' ++ [S']))
          = π (E.pos (h₀ ++ reqMap G (χ' ++ [S']))) :=
        shadowFrom_pos n π G hG hGne E h₀ hh (by simp)
      have hpos2 : (shadowFrom n π G hG hGne E h₀).pos (h ++ (χ' ++ [S'] ++ [S]))
          = π (E.pos (h₀ ++ reqMap G (χ' ++ [S'] ++ [S]))) :=
        shadowFrom_pos n π G hG hGne E h₀ hh (by simp)
      have hassoc : h ++ (χ' ++ [S']) ++ [S] = h ++ (χ' ++ [S'] ++ [S]) := by
        rw [List.append_assoc]
      have hassoc2 : h₀ ++ reqMap G (χ' ++ [S']) ++ [G S]
          = h₀ ++ reqMap G (χ' ++ [S'] ++ [S]) := by
        rw [List.append_assoc]
        congr 1
        rw [reqMap_append (G := G) (l := χ' ++ [S']) (l' := [S])]
        rfl
      rw [hassoc, hpos1, hpos2, hassoc2]
      simp only [List.concat_eq_append] at ih
      have hlip := hπ (E.pos (h₀ ++ reqMap G (χ' ++ [S'])))
        (E.pos (h₀ ++ reqMap G (χ' ++ [S'] ++ [S])))
      linarith [ih]


private theorem find?_congr4 {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases q a
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    · rfl

/-- Bail times transport along the offset request transformation. -/
theorem shadowFrom_bailTime (n : ℕ) (G : Set X → Set Y)
    (bail' : List (Set Y) → Bool) (h₀ : List (Set Y)) (h χ : List (Set X))
    (hh : h.length = n) :
    bailTime (fun l => bail' (h₀ ++ reqMap G (l.drop n))) h χ
      = bailTime bail' h₀ (reqMap G χ) := by
  unfold bailTime
  rw [reqMap_length]
  refine find?_congr4 _ _ _ fun q _ => ?_
  show bail' (h₀ ++ reqMap G ((h ++ χ.take q).drop n)) = _
  rw [drop_exact hh, reqMap_take]

/-- **Offset shadow bail-cost domination** (chunk-only, aligned start). -/
theorem shadowFrom_bailCost_le (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (bail' : List (Set Y) → Bool)
    (h₀ : List (Set Y)) (h χ : List (Set X)) {pe p' : ℝ} (hpe : pe ≤ p')
    (hh : h.length = n)
    (hstart : (shadowFrom n π G hG hGne E h₀).pos h = π (E.pos h₀)) :
    (shadowFrom n π G hG hGne E h₀).bailCost
        (fun l => bail' (h₀ ++ reqMap G (l.drop n))) h χ pe
      ≤ E.bailCost bail' h₀ (reqMap G χ) p' := by
  unfold EvaderAlgorithm.bailCost
  rw [shadowFrom_bailTime n G bail' h₀ h χ hh]
  rcases hq : bailTime bail' h₀ (reqMap G χ) with - | q
  · exact shadowFrom_costOn_le n π G hπ hG hGne E h₀ h χ hh hstart
  · have h1 := shadowFrom_costOn_le n π G hπ hG hGne E h₀ h (χ.take q) hh hstart
    rw [reqMap_take] at h1
    linarith


section ParkFrom

open Classical in
/-- The offset park-aware shadow. -/
noncomputable def parkShadowFrom (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (Pk : Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) : EvaderAlgorithm X where
  pos l :=
    if E.pos (h₀ ++ parkMap G Pk (l.drop n)) ∈ Pk then
      match l.getLast? with
      | some S => if hS : S.Nonempty then hS.choose
          else π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
      | none => π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
    else if l.length ≤ n then
      match l.getLast? with
      | some S =>
          if π (E.pos (h₀ ++ parkMap G Pk (l.drop n))) ∈ S then
            π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
          else if hS : S.Nonempty then hS.choose
          else π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
      | none => π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
    else π (E.pos (h₀ ++ parkMap G Pk (l.drop n)))
  serves l S hS := by
    have hlast : (l ++ [S]).getLast? = some S := List.getLast?_concat
    by_cases hp : E.pos (h₀ ++ parkMap G Pk ((l ++ [S]).drop n)) ∈ Pk
    · simp only [hp, if_pos, hlast]
      rw [dif_pos hS]
      exact hS.choose_spec
    · simp only [hp, if_neg, not_false_iff]
      by_cases hlen : (l ++ [S]).length ≤ n
      · simp only [hlen, if_pos, hlast]
        by_cases hmem : π (E.pos (h₀ ++ parkMap G Pk ((l ++ [S]).drop n))) ∈ S
        · rw [if_pos hmem]
          exact hmem
        · rw [if_neg hmem, dif_pos hS]
          exact hS.choose_spec
      · simp only [hlen, if_neg, not_false_iff]
        have hlen2 : n ≤ l.length := by
          have h1 : (l ++ [S]).length = l.length + 1 := by simp
          omega
        have hdrop : (l ++ [S]).drop n = l.drop n ++ [S] :=
          List.drop_append_of_le_length hlen2
        rw [hdrop, parkMap_append, ← List.append_assoc]
        have hserve := E.serves (h₀ ++ parkMap G Pk (l.drop n)) (G S ∪ Pk)
          (Set.Nonempty.inl (hGne S hS))
        rw [hdrop, parkMap_append, ← List.append_assoc] at hp
        rcases hserve with hin | hin
        · exact hG S _ hin
        · exact absurd hin (by
            show E.pos ((h₀ ++ parkMap G Pk (l.drop n))
              ++ parkMap G Pk [S]) ∈ Pk → False
            exact hp)

end ParkFrom


section ParkFromMain

open Classical in
/-- Out-of-park positions of the offset park shadow beyond the boundary. -/
theorem parkShadowFrom_pos_out (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (Pk : Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h χ : List (Set X)}
    (hh : h.length = n) {q : ℕ} (hq1 : 1 ≤ q) (hqlen : q ≤ χ.length)
    (hout : E.pos (h₀ ++ (parkMap G Pk χ).take q) ∉ Pk) :
    (parkShadowFrom n π G Pk hG hGne E h₀).pos (h ++ χ.take q)
      = π (E.pos (h₀ ++ (parkMap G Pk χ).take q)) := by
  have halign : (h ++ χ.take q).drop n = χ.take q := drop_exact hh
  have hcond : E.pos (h₀ ++ parkMap G Pk ((h ++ χ.take q).drop n))
      = E.pos (h₀ ++ (parkMap G Pk χ).take q) := by
    rw [halign, parkMap_take]
  have hlen : ¬ (h ++ χ.take q).length ≤ n := by
    have h1 : (h ++ χ.take q).length = n + (χ.take q).length := by
      simp [hh]
    have h2 : (χ.take q).length = min q χ.length := by simp
    omega
  unfold parkShadowFrom
  show (if E.pos (h₀ ++ parkMap G Pk ((h ++ χ.take q).drop n)) ∈ Pk
    then _ else _) = _
  rw [hcond, if_neg hout, if_neg hlen]

open Classical in
/-- Parked positions of the offset park shadow. -/
theorem parkShadowFrom_pos_in (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (Pk : Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h χ : List (Set X)}
    (hh : h.length = n) {q : ℕ} (hq : q < χ.length)
    (hSne : (χ[q] : Set X).Nonempty)
    (hin : E.pos (h₀ ++ (parkMap G Pk χ).take (q + 1)) ∈ Pk) :
    (parkShadowFrom n π G Pk hG hGne E h₀).pos (h ++ χ.take (q + 1))
      = hSne.choose := by
  have halign : (h ++ χ.take (q + 1)).drop n = χ.take (q + 1) := drop_exact hh
  have hcond : E.pos (h₀ ++ parkMap G Pk ((h ++ χ.take (q + 1)).drop n))
      = E.pos (h₀ ++ (parkMap G Pk χ).take (q + 1)) := by
    rw [halign, parkMap_take]
  unfold parkShadowFrom
  show (if E.pos (h₀ ++ parkMap G Pk ((h ++ χ.take (q + 1)).drop n)) ∈ Pk
    then _ else _) = _
  rw [hcond, if_pos hin]
  have hlast : (h ++ χ.take (q + 1)).getLast? = some (χ[q] : Set X) := by
    rw [KServer.take_succ_chunk χ hq, ← List.append_assoc, List.getLast?_concat]
  rw [hlast]
  show (if hS : (χ[q] : Set X).Nonempty then hS.choose else _) = _
  rw [dif_pos hSne]

end ParkFromMain


section ParkFromBail

open Classical in
/-- **Offset park-shadow bail-cost domination** (chunk-only, aligned
start): the race's side premise instantiation for coin-phase chunks. -/
theorem parkShadowFrom_bailCost_le (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (Pk : Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (bail' : List (Set Y) → Bool)
    (h₀ : List (Set Y)) (h χ : List (Set X)) {pe p' sep J : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hsep : ∀ (S : Set X) (y z : Y), y ∈ G S → z ∈ Pk → sep ≤ dist y z)
    (hstartPk : ∀ z ∈ Pk, sep ≤ dist (E.pos h₀) z)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J)
    (harith : J + pe ≤ sep)
    (hchunk : ∀ q : ℕ, (hq : q < χ.length) → (χ[q] : Set X).Nonempty)
    (hh : h.length = n)
    (hstart : (parkShadowFrom n π G Pk hG hGne E h₀).pos h
      = π (E.pos h₀)) :
    (parkShadowFrom n π G Pk hG hGne E h₀).bailCost
        (fun l => bail' (h₀ ++ parkMap G Pk (l.drop n))
          || decide (E.pos (h₀ ++ parkMap G Pk (l.drop n)) ∈ Pk)) h χ pe
      ≤ E.bailCost bail' h₀ (parkMap G Pk χ) p' := by
  set SH := parkShadowFrom n π G Pk hG hGne E h₀ with hSH_def
  set PY : ℕ → Y := fun q => E.pos (h₀ ++ (parkMap G Pk χ).take q) with hPY_def
  have hp'0 : 0 ≤ p' := le_trans hpe0 hpe
  have hpos0 : PY 0 ∉ Pk := by
    intro hmem
    have h1 := hstartPk _ hmem
    have h2 : PY 0 = E.pos h₀ := by
      rw [hPY_def]
      simp
    rw [h2] at hmem
    have h3 := hstartPk _ hmem
    rw [dist_self] at h3
    linarith
  have hPY0 : PY 0 = E.pos h₀ := by
    rw [hPY_def]
    simp
  have hlenP : (parkMap G Pk χ).length = χ.length := parkMap_length G Pk χ
  -- bail components at aligned prefixes
  have hbailI_at : ∀ q : ℕ,
      (bail' (h₀ ++ parkMap G Pk ((h ++ χ.take q).drop n))
        || decide (E.pos (h₀ ++ parkMap G Pk ((h ++ χ.take q).drop n)) ∈ Pk))
      = (bail' (h₀ ++ (parkMap G Pk χ).take q) || decide (PY q ∈ Pk)) := by
    intro q
    rw [drop_exact hh, parkMap_take]
  -- serving discipline in the mapped requests
  have hposmem : ∀ q : ℕ, (hq : q < χ.length) →
      PY (q + 1) ∈ G (χ[q]'hq) ∪ Pk := by
    intro q hq
    rw [hPY_def]
    show E.pos (h₀ ++ (parkMap G Pk χ).take (q + 1)) ∈ _
    rw [KServer.take_succ_park G Pk χ hq, ← List.append_assoc]
    exact E.serves _ _ (Set.Nonempty.inl (hGne _ (hchunk q hq)))
  have hposG : ∀ q : ℕ, (hq : q < χ.length) → PY (q + 1) ∉ Pk →
      PY (q + 1) ∈ G (χ[q]'hq) := by
    intro q hq hout
    exact (hposmem q hq).resolve_right hout
  -- E-side step expansion
  have hEstep : ∀ q : ℕ, (hq : q < χ.length) →
      E.costOn h₀ ((parkMap G Pk χ).take (q + 1))
        = E.costOn h₀ ((parkMap G Pk χ).take q)
          + dist (PY q) (PY (q + 1)) := by
    intro q hq
    rw [KServer.take_succ_park G Pk χ hq, E.costOn_concat]
    have h2 : E.pos (h₀ ++ (parkMap G Pk χ).take q
        ++ [G (χ[q]'hq) ∪ Pk]) = PY (q + 1) := by
      rw [List.append_assoc, ← KServer.take_succ_park G Pk χ hq]
    rw [h2]
    try rfl
  -- shadow step expansion
  have hSstep : ∀ q : ℕ, (hq : q < χ.length) →
      SH.costOn h (χ.take (q + 1))
        = SH.costOn h (χ.take q)
          + dist (SH.pos (h ++ χ.take q)) (SH.pos (h ++ χ.take (q + 1))) := by
    intro q hq
    rw [KServer.take_succ_chunk χ hq, SH.costOn_concat]
    have h2 : SH.pos (h ++ (χ.take q ++ [χ[q]'hq]))
        = SH.pos (h ++ χ.take (q + 1)) := by
      rw [← KServer.take_succ_chunk χ hq]
    rw [← List.append_assoc, List.append_assoc, h2]
  -- entry steps are expensive
  have hentry : ∀ q : ℕ, (hq : q < χ.length) → PY q ∉ Pk → PY (q + 1) ∈ Pk →
      sep ≤ dist (PY q) (PY (q + 1)) := by
    intro q hq hout hin
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · rw [hPY0]
      exact hstartPk _ hin
    · obtain ⟨q', rfl⟩ : ∃ q'', q = q'' + 1 := ⟨q - 1, by omega⟩
      have hinG : PY (q' + 1) ∈ G (χ[q']'(by omega)) := hposG q' (by omega) hout
      exact hsep _ _ _ hinG hin
  -- shadow position facts
  have hSout : ∀ q : ℕ, q ≤ χ.length → PY q ∉ Pk →
      SH.pos (h ++ χ.take q) = π (PY q) := by
    intro q hq hout
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · rw [List.take_zero, List.append_nil, hstart, hPY0]
    · exact parkShadowFrom_pos_out n π G Pk hG hGne E h₀ hh hqpos hq hout
  -- master prefix domination
  have hmaster : ∀ m : ℕ, m ≤ χ.length →
      (∀ q, 1 ≤ q → q < m → PY q ∉ Pk) →
      SH.costOn h (χ.take m) ≤ E.costOn h₀ ((parkMap G Pk χ).take m) := by
    intro m
    induction m with
    | zero =>
      intro _ _
      rw [List.take_zero, List.take_zero]
      have h1 : SH.costOn h [] = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil, sub_self]
      have h2 : E.costOn h₀ ([] : List (Set Y)) = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil, sub_self]
      rw [h1, h2]
    | succ m ih =>
      intro hm hint
      have hmlt : m < χ.length := by omega
      have hleft : PY m ∉ Pk := by
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · exact hpos0
        · exact hint m hmpos (by omega)
      have hIH := ih (by omega) (fun q h1 h2 => hint q h1 (by omega))
      rw [hSstep m hmlt, hEstep m hmlt]
      have hposout := hSout m (by omega) hleft
      by_cases hinq : PY (m + 1) ∈ Pk
      · have hSpos := parkShadowFrom_pos_in n π G Pk hG hGne E h₀ hh hmlt
          (hchunk m hmlt) (by exact hinq)
        rw [hposout, hSpos]
        have h1 : dist (π (PY m)) (hchunk m hmlt).choose ≤ J := hdiam _ _
        have h2 := hentry m hmlt hleft hinq
        linarith
      · have hSpos' := hSout (m + 1) (by omega) hinq
        rw [hposout, hSpos']
        have h1 := hπ (PY m) (PY (m + 1))
        linarith
  -- E-cost monotonicity
  have hEmono : ∀ q q' : ℕ, q ≤ q' →
      E.costOn h₀ ((parkMap G Pk χ).take q)
        ≤ E.costOn h₀ ((parkMap G Pk χ).take q') := by
    intro q q' hqq
    have hsplit : (parkMap G Pk χ).take q' = ((parkMap G Pk χ).take q').take q
        ++ (((parkMap G Pk χ).take q').drop q) := (List.take_append_drop _ _).symm
    rw [List.take_take, min_eq_left hqq] at hsplit
    rw [hsplit, E.costOn_append]
    have := E.costOn_nonneg (h₀ ++ (parkMap G Pk χ).take q)
      (((parkMap G Pk χ).take q').drop q)
    linarith
  -- main case analysis
  unfold EvaderAlgorithm.bailCost
  rcases hQI : bailTime (fun l => bail' (h₀ ++ parkMap G Pk (l.drop n))
      || decide (E.pos (h₀ ++ parkMap G Pk (l.drop n)) ∈ Pk)) h χ with _ | q
  · have hall := KServer.bailTime_none_iff.mp hQI
    have hEnone : bailTime bail' h₀ (parkMap G Pk χ) = none := by
      rw [KServer.bailTime_none_iff]
      intro q hq
      rw [hlenP] at hq
      have h1 := hall q hq
      rw [hbailI_at q] at h1
      exact (Bool.or_eq_false_iff.mp h1).1
    rw [hEnone]
    have hint : ∀ q, 1 ≤ q → q < χ.length → PY q ∉ Pk := by
      intro q h1 h2
      have := hall q h2
      rw [hbailI_at q] at this
      have h3 := (Bool.or_eq_false_iff.mp this).2
      simpa using h3
    have := hmaster χ.length (le_refl _) hint
    rw [List.take_length] at this
    rw [show (parkMap G Pk χ).take χ.length = parkMap G Pk χ by
      rw [← hlenP, List.take_length]] at this
    exact this
  · obtain ⟨hqlen, hfire, hbefore⟩ := KServer.bailTime_some_first hQI
    have hint : ∀ q', 1 ≤ q' → q' < q → PY q' ∉ Pk := by
      intro q' h1 h2
      have := hbefore q' h2
      rw [hbailI_at q'] at this
      have h3 := (Bool.or_eq_false_iff.mp this).2
      simpa using h3
    have hbefore' : ∀ q', q' < q →
        bail' (h₀ ++ (parkMap G Pk χ).take q') = false := by
      intro q' h2
      have := hbefore q' h2
      rw [hbailI_at q'] at this
      exact (Bool.or_eq_false_iff.mp this).1
    rw [hbailI_at q] at hfire
    rcases Bool.or_eq_true_iff.mp hfire with hb' | hpk
    · have hEfire : bailTime bail' h₀ (parkMap G Pk χ) = some q := by
        refine KServer.bailTime_some_intro (by rw [hlenP]; exact hqlen) hb' ?_
        intro q' h2
        exact hbefore' q' h2
      rw [hEfire]
      have hmq := hmaster q (le_of_lt hqlen) hint
      linarith
    · have hinPk : PY q ∈ Pk := of_decide_eq_true hpk
      have hqpos : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | h1
        · exact absurd hinPk hpos0
        · exact h1
      have hleft : PY (q - 1) ∉ Pk := by
        rcases Nat.eq_zero_or_pos (q - 1) with h0 | h1
        · rw [h0]
          exact hpos0
        · exact hint (q - 1) h1 (by omega)
      have hq1len : q - 1 < χ.length := by omega
      have hmq1 := hmaster (q - 1) (by omega) (fun a h1 h2 => hint a h1 (by omega))
      have hSsplit := hSstep (q - 1) hq1len
      rw [show q - 1 + 1 = q by omega] at hSsplit
      have hEsplit := hEstep (q - 1) hq1len
      rw [show q - 1 + 1 = q by omega] at hEsplit
      have hjump : dist (SH.pos (h ++ χ.take (q - 1))) (SH.pos (h ++ χ.take q))
          ≤ J := by
        have hposout := hSout (q - 1) (by omega) hleft
        have hSpos := parkShadowFrom_pos_in n π G Pk hG hGne E h₀ hh hq1len
          (hchunk _ hq1len) (by
            rw [show q - 1 + 1 = q by omega]
            exact hinPk)
        rw [show q - 1 + 1 = q by omega] at hSpos
        rw [hposout, hSpos]
        exact hdiam _ _
      have hcross : sep ≤ dist (PY (q - 1)) (PY q) := by
        have := hentry (q - 1) hq1len hleft
          (by rw [show q - 1 + 1 = q by omega]; exact hinPk)
        rwa [show q - 1 + 1 = q by omega] at this
      have hEge : E.costOn h₀ ((parkMap G Pk χ).take q)
          ≤ E.bailCost bail' h₀ (parkMap G Pk χ) p' := by
        unfold EvaderAlgorithm.bailCost
        rcases hE : bailTime bail' h₀ (parkMap G Pk χ) with _ | q''
        · have h1 := hEmono q χ.length (le_of_lt hqlen)
          rw [show (parkMap G Pk χ).take χ.length = parkMap G Pk χ by
            rw [← hlenP, List.take_length]] at h1
          exact h1
        · obtain ⟨hq''len, hfire'', hbefore''⟩ := KServer.bailTime_some_first hE
          have hq''ge : q ≤ q'' := by
            by_contra hcon
            push_neg at hcon
            have := hbefore' q'' hcon
            rw [this] at hfire''
            exact absurd hfire'' (by simp)
          have h1 := hEmono q q'' hq''ge
          linarith
      unfold EvaderAlgorithm.bailCost at hEge
      calc SH.costOn h (χ.take q) + pe
          = SH.costOn h (χ.take (q - 1))
            + dist (SH.pos (h ++ χ.take (q - 1))) (SH.pos (h ++ χ.take q))
            + pe := by rw [← hSsplit]
        _ ≤ E.costOn h₀ ((parkMap G Pk χ).take (q - 1)) + J + pe := by
            linarith
        _ ≤ E.costOn h₀ ((parkMap G Pk χ).take (q - 1)) + sep := by linarith
        _ ≤ E.costOn h₀ ((parkMap G Pk χ).take q) := by
            rw [hEsplit]
            linarith
        _ ≤ E.bailCost bail' h₀ (parkMap G Pk χ) p' := hEge

end ParkFromBail

end KServer


