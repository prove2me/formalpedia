-- Prove2me | solution 1 for AlmostLossless.honest_scanCode
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:07:51.244103+00:00
-- url     : https://prove2.me/submissions/4867d11d-187d-4b88-92a6-5bca27c837e5

import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme

open AlmostLossless

open AlmostLossless in
/-- **The scan decoder is honest**: it returns the encoded word or declares failure. -/
theorem solution {S A M : Type*} [DecidableEq S] [DecidableEq M] (P : ScanScheme S A M) (a : A) :
    Honest (P.code a) := by
  have scanU : ∀ (p : S → Bool) (L : List S) (t : S),
      scan p L = .unique t ↔ L.filter p = [t] := by
    intro p L t
    have hstep : ∀ (K : List S) (st : ScanState S),
        K.foldl (scanStep p) st = (K.filter p).foldl scanStepAll st := by
      intro K
      induction K with
      | nil => intro st; simp
      | cons b K ih =>
          intro st
          cases h : p b <;> simp [List.filter_cons, h, scanStep, scanStepAll, ih]
    have amb : ∀ (N : List S), N.foldl scanStepAll ScanState.ambiguous = .ambiguous := by
      intro N
      induction N with
      | nil => rfl
      | cons b N ih => simpa [scanStepAll] using ih
    have hfold : ∀ (N : List S), N.foldl scanStepAll ScanState.empty = .unique t ↔ N = [t] := by
      intro N
      match N with
      | [] => simp
      | [b] => simp [scanStepAll]
      | b :: c :: N' => simp [scanStepAll, amb]
    rw [scan, hstep L ScanState.empty]
    exact hfold (L.filter p)
  intro s
  by_cases hs : s ∈ P.typical
  · have henc : (P.code a).enc s = some (P.hash a s) := by simp [ScanScheme.code, hs]
    have hdec : (P.code a).dec (some (P.hash a s)) = P.decode a (P.hash a s) := rfl
    rw [henc, hdec]
    unfold ScanScheme.decode
    split
    · rename_i t ht
      left
      have hf := (scanU _ _ _).mp ht
      have hmem : s ∈ (P.cand a (P.hash a s)).toList.filter (fun u => decide (P.hash a u = P.hash a s)) := by
        simp [P.self_mem_cand a s hs]
      rw [hf, List.mem_singleton] at hmem
      rw [hmem]
    · right; rfl
  · right
    have henc : (P.code a).enc s = none := by simp [ScanScheme.code, hs]
    rw [henc]
    rfl
