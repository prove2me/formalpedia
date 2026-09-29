-- Prove2me | solution 1 for berggrenAt_pyth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:58.765464+00:00
-- url     : https://prove2.me/submissions/07965504-c129-4018-942a-b379e48107bf

-- Sol generated from Geometry/BerggrenRamanujan.lean
import Mathlib
import Definitions.Def_Geometry_BerggrenRamanujan

open Matrix

/-! # CatalogBuild.Pythagorean.Berggren.BerggrenRamanujan

Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 59
-/

noncomputable section





/-- Each Berggren step preserves the Pythagorean equation. -/
theorem berggrenStep_preserves_pyth (d : BDir) (a b c : ℤ)
    (h : a ^ 2 + b ^ 2 = c ^ 2) :
    let (a', b', c') := berggrenStep d (a, b, c)
    a' ^ 2 + b' ^ 2 = c' ^ 2 := by
  cases d <;> simp [berggrenStep] <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
























































theorem solution(path : BPos) :
    let (a, b, c) := berggrenAt path
    a ^ 2 + b ^ 2 = c ^ 2 := by
  simp only [berggrenAt]
  suffices h : ∀ (t : ℤ × ℤ × ℤ), t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 →
    let r := path.foldl (fun t d => berggrenStep d t) t
    r.1 ^ 2 + r.2.1 ^ 2 = r.2.2 ^ 2 from
    h (3, 4, 5) (by norm_num)
  intro t ht
  induction path generalizing t with
  | nil => exact ht
  | cons d ds ih =>
    simp only [List.foldl]
    apply ih
    exact berggrenStep_preserves_pyth d t.1 t.2.1 t.2.2 ht
