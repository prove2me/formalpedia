-- Prove2me | solution 1 for GeneratorTilt.deployed_descending_wins
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:53:56.389547+00:00
-- url     : https://prove2.me/submissions/62e43c47-0c0b-4f78-9bbd-b0558743c510

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
import Definitions.Def_Novelty_GeneratorTiltSynthesis
import Definitions.Def_Novelty_GeneratorTiltWindow

open GeneratorTilt in
theorem solution {n : ℤ} {q : ℝ} (hp : 0 < (n : ℝ)) (hq : 0 < q)
    (hN : 1 ≤ 2 * margin (q / (n : ℝ)) * Real.sqrt ((n : ℝ) * q)) :
    descCost ⌊Real.sqrt ((n : ℝ) * q)⌋ n < ascCost ⌈Real.sqrt ((n : ℝ) * q / 2)⌉ n := by
  set s := Real.sqrt ((n : ℝ) * q) with hs
  set s2 := Real.sqrt ((n : ℝ) * q / 2) with hs2
  -- the margin condition says `s + s2 ≤ 2n - 1`
  have hn0 : (n : ℝ) ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  have hA : s / Real.sqrt (q / n) = n := by
    rw [hs, ← Real.sqrt_div (by positivity : (0 : ℝ) ≤ n * q) (q / n)]
    have h1 : (n : ℝ) * q / (q / n) = (n : ℝ) ^ 2 := by
      field_simp
    rw [h1, Real.sqrt_sq hp.le]
  have hB : s * (1 / Real.sqrt 2) = s2 := by
    rw [hs, hs2, Real.sqrt_div (by positivity : (0 : ℝ) ≤ n * q) 2]
    ring
  have hmargin : 2 * margin (q / (n : ℝ)) * s = 2 * n - s - s2 := by
    rw [margin]
    have h2 : 2 * (1 / Real.sqrt (q / n) - (1 + 1 / Real.sqrt 2) / 2) * s
        = 2 * (s / Real.sqrt (q / n)) - s - s * (1 / Real.sqrt 2) := by
      ring
    rw [h2, hA, hB]
  rw [hmargin] at hN
  -- floors and ceilings lose less than one in total
  have hfl : ((⌊s⌋ : ℤ) : ℝ) ≤ s := Int.floor_le s
  have hce : ((⌈s2⌉ : ℤ) : ℝ) < s2 + 1 := Int.ceil_lt_add_one s2
  have hint : ((⌊s⌋ + ⌈s2⌉ : ℤ) : ℝ) < ((2 * n : ℤ) : ℝ) := by
    push_cast
    linarith
  have hint' : ⌊s⌋ + ⌈s2⌉ < 2 * n := by exact_mod_cast hint
  unfold descCost ascCost
  omega
